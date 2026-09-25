import Mathlib
import Submission.Work.RHContract.A.RegionI.Data10

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma s2L_2502 : ((((452243344329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22349 < q → q < 22367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22367).mp (by decide +kernel))) hgap
  have hprev := s2L_2501
  have hrat : ((452243344329 : ℚ) / 1000000000000) ≤ ((452243342331 : ℚ) / 1000000000000) + (22367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243344329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243342331 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22367:ℚ)^(-2:ℤ) : ℝ) = ((22367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2503 : ((((452243346327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22367 < q → q < 22369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22369).mp (by decide +kernel))) hgap
  have hprev := s2L_2502
  have hrat : ((452243346327 : ℚ) / 1000000000000) ≤ ((452243344329 : ℚ) / 1000000000000) + (22369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243346327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243344329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22369:ℚ)^(-2:ℤ) : ℝ) = ((22369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2504 : ((((452243348323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22369 < q → q < 22381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22381).mp (by decide +kernel))) hgap
  have hprev := s2L_2503
  have hrat : ((452243348323 : ℚ) / 1000000000000) ≤ ((452243346327 : ℚ) / 1000000000000) + (22381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243348323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243346327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22381:ℚ)^(-2:ℤ) : ℝ) = ((22381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2505 : ((((452243350317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22381 < q → q < 22391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22391).mp (by decide +kernel))) hgap
  have hprev := s2L_2504
  have hrat : ((452243350317 : ℚ) / 1000000000000) ≤ ((452243348323 : ℚ) / 1000000000000) + (22391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243350317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243348323 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22391:ℚ)^(-2:ℤ) : ℝ) = ((22391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2506 : ((((45224335231 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22391 < q → q < 22397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22397).mp (by decide +kernel))) hgap
  have hprev := s2L_2505
  have hrat : ((45224335231 : ℚ) / 100000000000) ≤ ((452243350317 : ℚ) / 1000000000000) + (22397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224335231 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243350317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22397:ℚ)^(-2:ℤ) : ℝ) = ((22397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2507 : ((((452243354301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22397 < q → q < 22409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22409).mp (by decide +kernel))) hgap
  have hprev := s2L_2506
  have hrat : ((452243354301 : ℚ) / 1000000000000) ≤ ((45224335231 : ℚ) / 100000000000) + (22409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243354301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224335231 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22409:ℚ)^(-2:ℤ) : ℝ) = ((22409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2508 : ((((3533151221 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22409 < q → q < 22433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22433).mp (by decide +kernel))) hgap
  have hprev := s2L_2507
  have hrat : ((3533151221 : ℚ) / 7812500000) ≤ ((452243354301 : ℚ) / 1000000000000) + (22433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533151221 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((452243354301 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22433:ℚ)^(-2:ℤ) : ℝ) = ((22433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2509 : ((((452243358273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22433 < q → q < 22441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22441).mp (by decide +kernel))) hgap
  have hprev := s2L_2508
  have hrat : ((452243358273 : ℚ) / 1000000000000) ≤ ((3533151221 : ℚ) / 7812500000) + (22441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243358273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3533151221 : ℚ) / 7812500000) : ℚ) : ℝ) + ((22441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22441:ℚ)^(-2:ℤ) : ℝ) = ((22441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2510 : ((((452243360257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22441 < q → q < 22447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22447).mp (by decide +kernel))) hgap
  have hprev := s2L_2509
  have hrat : ((452243360257 : ℚ) / 1000000000000) ≤ ((452243358273 : ℚ) / 1000000000000) + (22447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243360257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243358273 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22447:ℚ)^(-2:ℤ) : ℝ) = ((22447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2511 : ((((1413260507 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22447 < q → q < 22453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22453).mp (by decide +kernel))) hgap
  have hprev := s2L_2510
  have hrat : ((1413260507 : ℚ) / 3125000000) ≤ ((452243360257 : ℚ) / 1000000000000) + (22453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1413260507 : ℚ) / 3125000000) : ℚ) : ℝ) ≤ ((((452243360257 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22453:ℚ)^(-2:ℤ) : ℝ) = ((22453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2512 : ((((22612168211 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22453 < q → q < 22469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22469).mp (by decide +kernel))) hgap
  have hprev := s2L_2511
  have hrat : ((22612168211 : ℚ) / 50000000000) ≤ ((1413260507 : ℚ) / 3125000000) + (22469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612168211 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((1413260507 : ℚ) / 3125000000) : ℚ) : ℝ) + ((22469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22469:ℚ)^(-2:ℤ) : ℝ) = ((22469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2513 : ((((226121683099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22469 < q → q < 22481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22481).mp (by decide +kernel))) hgap
  have hprev := s2L_2512
  have hrat : ((226121683099 : ℚ) / 500000000000) ≤ ((22612168211 : ℚ) / 50000000000) + (22481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121683099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612168211 : ℚ) / 50000000000) : ℚ) : ℝ) + ((22481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22481:ℚ)^(-2:ℤ) : ℝ) = ((22481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2514 : ((((28265210511 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22481 < q → q < 22483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22483).mp (by decide +kernel))) hgap
  have hprev := s2L_2513
  have hrat : ((28265210511 : ℚ) / 62500000000) ≤ ((226121683099 : ℚ) / 500000000000) + (22483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265210511 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121683099 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22483:ℚ)^(-2:ℤ) : ℝ) = ((22483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2515 : ((((452243370151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22483 < q → q < 22501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22501).mp (by decide +kernel))) hgap
  have hprev := s2L_2514
  have hrat : ((452243370151 : ℚ) / 1000000000000) ≤ ((28265210511 : ℚ) / 62500000000) + (22501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243370151 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265210511 : ℚ) / 62500000000) : ℚ) : ℝ) + ((22501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22501:ℚ)^(-2:ℤ) : ℝ) = ((22501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2516 : ((((113060843031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22501 < q → q < 22511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22511).mp (by decide +kernel))) hgap
  have hprev := s2L_2515
  have hrat : ((113060843031 : ℚ) / 250000000000) ≤ ((452243370151 : ℚ) / 1000000000000) + (22511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060843031 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243370151 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22511:ℚ)^(-2:ℤ) : ℝ) = ((22511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2517 : ((((452243374093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22511 < q → q < 22531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22531).mp (by decide +kernel))) hgap
  have hprev := s2L_2516
  have hrat : ((452243374093 : ℚ) / 1000000000000) ≤ ((113060843031 : ℚ) / 250000000000) + (22531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243374093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060843031 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22531:ℚ)^(-2:ℤ) : ℝ) = ((22531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2518 : ((((452243376061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22531 < q → q < 22541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22541).mp (by decide +kernel))) hgap
  have hprev := s2L_2517
  have hrat : ((452243376061 : ℚ) / 1000000000000) ≤ ((452243374093 : ℚ) / 1000000000000) + (22541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243376061 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243374093 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22541:ℚ)^(-2:ℤ) : ℝ) = ((22541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2519 : ((((113060844507 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22541 < q → q < 22543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22543).mp (by decide +kernel))) hgap
  have hprev := s2L_2518
  have hrat : ((113060844507 : ℚ) / 250000000000) ≤ ((452243376061 : ℚ) / 1000000000000) + (22543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060844507 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243376061 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22543:ℚ)^(-2:ℤ) : ℝ) = ((22543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2520 : ((((226121689997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22543 < q → q < 22549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22549).mp (by decide +kernel))) hgap
  have hprev := s2L_2519
  have hrat : ((226121689997 : ℚ) / 500000000000) ≤ ((113060844507 : ℚ) / 250000000000) + (22549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121689997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060844507 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22549:ℚ)^(-2:ℤ) : ℝ) = ((22549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2521 : ((((452243381957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22549 < q → q < 22567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22567).mp (by decide +kernel))) hgap
  have hprev := s2L_2520
  have hrat : ((452243381957 : ℚ) / 1000000000000) ≤ ((226121689997 : ℚ) / 500000000000) + (22567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243381957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121689997 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22567:ℚ)^(-2:ℤ) : ℝ) = ((22567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2522 : ((((452243383919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22567 < q → q < 22571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22571).mp (by decide +kernel))) hgap
  have hprev := s2L_2521
  have hrat : ((452243383919 : ℚ) / 1000000000000) ≤ ((452243381957 : ℚ) / 1000000000000) + (22571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243383919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243381957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22571:ℚ)^(-2:ℤ) : ℝ) = ((22571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2523 : ((((452243385881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22571 < q → q < 22573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22573).mp (by decide +kernel))) hgap
  have hprev := s2L_2522
  have hrat : ((452243385881 : ℚ) / 1000000000000) ≤ ((452243383919 : ℚ) / 1000000000000) + (22573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243385881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243383919 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22573:ℚ)^(-2:ℤ) : ℝ) = ((22573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2524 : ((((113060846959 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22573 < q → q < 22613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22613).mp (by decide +kernel))) hgap
  have hprev := s2L_2523
  have hrat : ((113060846959 : ℚ) / 250000000000) ≤ ((452243385881 : ℚ) / 1000000000000) + (22613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060846959 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243385881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22613:ℚ)^(-2:ℤ) : ℝ) = ((22613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2525 : ((((45224338979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22613 < q → q < 22619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22619).mp (by decide +kernel))) hgap
  have hprev := s2L_2524
  have hrat : ((45224338979 : ℚ) / 100000000000) ≤ ((113060846959 : ℚ) / 250000000000) + (22619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224338979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060846959 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22619:ℚ)^(-2:ℤ) : ℝ) = ((22619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2526 : ((((1766575749 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22619 < q → q < 22621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22621).mp (by decide +kernel))) hgap
  have hprev := s2L_2525
  have hrat : ((1766575749 : ℚ) / 3906250000) ≤ ((45224338979 : ℚ) / 100000000000) + (22621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1766575749 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((45224338979 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22621:ℚ)^(-2:ℤ) : ℝ) = ((22621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2527 : ((((90448678739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22621 < q → q < 22637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22637).mp (by decide +kernel))) hgap
  have hprev := s2L_2526
  have hrat : ((90448678739 : ℚ) / 200000000000) ≤ ((1766575749 : ℚ) / 3906250000) + (22637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448678739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((1766575749 : ℚ) / 3906250000) : ℚ) : ℝ) + ((22637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22637:ℚ)^(-2:ℤ) : ℝ) = ((22637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2528 : ((((226121697823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22637 < q → q < 22639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22639).mp (by decide +kernel))) hgap
  have hprev := s2L_2527
  have hrat : ((226121697823 : ℚ) / 500000000000) ≤ ((90448678739 : ℚ) / 200000000000) + (22639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121697823 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448678739 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22639:ℚ)^(-2:ℤ) : ℝ) = ((22639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2529 : ((((113060849399 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22639 < q → q < 22643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22643).mp (by decide +kernel))) hgap
  have hprev := s2L_2528
  have hrat : ((113060849399 : ℚ) / 250000000000) ≤ ((226121697823 : ℚ) / 500000000000) + (22643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060849399 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121697823 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22643:ℚ)^(-2:ℤ) : ℝ) = ((22643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2530 : ((((90448679909 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22651, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22643 < q → q < 22651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22651).mp (by decide +kernel))) hgap
  have hprev := s2L_2529
  have hrat : ((90448679909 : ℚ) / 200000000000) ≤ ((113060849399 : ℚ) / 250000000000) + (22651:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448679909 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060849399 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22651:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22651:ℚ)^(-2:ℤ) : ℝ) = ((22651:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2531 : ((((45224340149 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22651 < q → q < 22669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22669).mp (by decide +kernel))) hgap
  have hprev := s2L_2530
  have hrat : ((45224340149 : ℚ) / 100000000000) ≤ ((90448679909 : ℚ) / 200000000000) + (22669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224340149 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90448679909 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22669:ℚ)^(-2:ℤ) : ℝ) = ((22669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2532 : ((((226121701717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22669 < q → q < 22679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22679).mp (by decide +kernel))) hgap
  have hprev := s2L_2531
  have hrat : ((226121701717 : ℚ) / 500000000000) ≤ ((45224340149 : ℚ) / 100000000000) + (22679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121701717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224340149 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22679:ℚ)^(-2:ℤ) : ℝ) = ((22679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2533 : ((((7066303209 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22679 < q → q < 22691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22691).mp (by decide +kernel))) hgap
  have hprev := s2L_2532
  have hrat : ((7066303209 : ℚ) / 15625000000) ≤ ((226121701717 : ℚ) / 500000000000) + (22691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066303209 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((226121701717 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22691:ℚ)^(-2:ℤ) : ℝ) = ((22691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2534 : ((((452243407317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22691 < q → q < 22697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22697).mp (by decide +kernel))) hgap
  have hprev := s2L_2533
  have hrat : ((452243407317 : ℚ) / 1000000000000) ≤ ((7066303209 : ℚ) / 15625000000) + (22697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243407317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066303209 : ℚ) / 15625000000) : ℚ) : ℝ) + ((22697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22697:ℚ)^(-2:ℤ) : ℝ) = ((22697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2535 : ((((452243409257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22697 < q → q < 22699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22699).mp (by decide +kernel))) hgap
  have hprev := s2L_2534
  have hrat : ((452243409257 : ℚ) / 1000000000000) ≤ ((452243407317 : ℚ) / 1000000000000) + (22699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243409257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243407317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22699:ℚ)^(-2:ℤ) : ℝ) = ((22699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2536 : ((((113060852799 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22699 < q → q < 22709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22709).mp (by decide +kernel))) hgap
  have hprev := s2L_2535
  have hrat : ((113060852799 : ℚ) / 250000000000) ≤ ((452243409257 : ℚ) / 1000000000000) + (22709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060852799 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243409257 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22709:ℚ)^(-2:ℤ) : ℝ) = ((22709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2537 : ((((452243413133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22709 < q → q < 22717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22717).mp (by decide +kernel))) hgap
  have hprev := s2L_2536
  have hrat : ((452243413133 : ℚ) / 1000000000000) ≤ ((113060852799 : ℚ) / 250000000000) + (22717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243413133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060852799 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22717:ℚ)^(-2:ℤ) : ℝ) = ((22717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2538 : ((((45224341507 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22717 < q → q < 22721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22721).mp (by decide +kernel))) hgap
  have hprev := s2L_2537
  have hrat : ((45224341507 : ℚ) / 100000000000) ≤ ((452243413133 : ℚ) / 1000000000000) + (22721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224341507 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243413133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22721:ℚ)^(-2:ℤ) : ℝ) = ((22721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2539 : ((((226121708503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22721 < q → q < 22727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22727).mp (by decide +kernel))) hgap
  have hprev := s2L_2538
  have hrat : ((226121708503 : ℚ) / 500000000000) ≤ ((45224341507 : ℚ) / 100000000000) + (22727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121708503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224341507 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22727:ℚ)^(-2:ℤ) : ℝ) = ((22727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2540 : ((((22612170947 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22727 < q → q < 22739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22739).mp (by decide +kernel))) hgap
  have hprev := s2L_2539
  have hrat : ((22612170947 : ℚ) / 50000000000) ≤ ((226121708503 : ℚ) / 500000000000) + (22739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612170947 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121708503 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22739:ℚ)^(-2:ℤ) : ℝ) = ((22739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2541 : ((((452243420873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22739 < q → q < 22741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22741).mp (by decide +kernel))) hgap
  have hprev := s2L_2540
  have hrat : ((452243420873 : ℚ) / 1000000000000) ≤ ((22612170947 : ℚ) / 50000000000) + (22741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243420873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612170947 : ℚ) / 50000000000) : ℚ) : ℝ) + ((22741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22741:ℚ)^(-2:ℤ) : ℝ) = ((22741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2542 : ((((113060855701 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22741 < q → q < 22751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22751).mp (by decide +kernel))) hgap
  have hprev := s2L_2541
  have hrat : ((113060855701 : ℚ) / 250000000000) ≤ ((452243420873 : ℚ) / 1000000000000) + (22751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060855701 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243420873 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22751:ℚ)^(-2:ℤ) : ℝ) = ((22751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2543 : ((((113060856183 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22769, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22751 < q → q < 22769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22769).mp (by decide +kernel))) hgap
  have hprev := s2L_2542
  have hrat : ((113060856183 : ℚ) / 250000000000) ≤ ((113060855701 : ℚ) / 250000000000) + (22769:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060856183 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060855701 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22769:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22769:ℚ)^(-2:ℤ) : ℝ) = ((22769:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2544 : ((((452243426659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22769 < q → q < 22777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22777).mp (by decide +kernel))) hgap
  have hprev := s2L_2543
  have hrat : ((452243426659 : ℚ) / 1000000000000) ≤ ((113060856183 : ℚ) / 250000000000) + (22777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243426659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060856183 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22777:ℚ)^(-2:ℤ) : ℝ) = ((22777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2545 : ((((90448685717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22777 < q → q < 22783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22783).mp (by decide +kernel))) hgap
  have hprev := s2L_2544
  have hrat : ((90448685717 : ℚ) / 200000000000) ≤ ((452243426659 : ℚ) / 1000000000000) + (22783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448685717 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243426659 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22783:ℚ)^(-2:ℤ) : ℝ) = ((22783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2546 : ((((45224343051 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22783 < q → q < 22787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22787).mp (by decide +kernel))) hgap
  have hprev := s2L_2545
  have hrat : ((45224343051 : ℚ) / 100000000000) ≤ ((90448685717 : ℚ) / 200000000000) + (22787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224343051 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90448685717 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22787:ℚ)^(-2:ℤ) : ℝ) = ((22787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2547 : ((((28265214527 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22787 < q → q < 22807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22807).mp (by decide +kernel))) hgap
  have hprev := s2L_2546
  have hrat : ((28265214527 : ℚ) / 62500000000) ≤ ((45224343051 : ℚ) / 100000000000) + (22807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265214527 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((45224343051 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22807:ℚ)^(-2:ℤ) : ℝ) = ((22807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2548 : ((((452243434353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22811, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22807 < q → q < 22811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22811).mp (by decide +kernel))) hgap
  have hprev := s2L_2547
  have hrat : ((452243434353 : ℚ) / 1000000000000) ≤ ((28265214527 : ℚ) / 62500000000) + (22811:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243434353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265214527 : ℚ) / 62500000000) : ℚ) : ℝ) + ((22811:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22811:ℚ)^(-2:ℤ) : ℝ) = ((22811:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2549 : ((((452243436273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22811 < q → q < 22817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22817).mp (by decide +kernel))) hgap
  have hprev := s2L_2548
  have hrat : ((452243436273 : ℚ) / 1000000000000) ≤ ((452243434353 : ℚ) / 1000000000000) + (22817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243436273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243434353 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22817:ℚ)^(-2:ℤ) : ℝ) = ((22817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2550 : ((((452243438187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22817 < q → q < 22853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22853).mp (by decide +kernel))) hgap
  have hprev := s2L_2549
  have hrat : ((452243438187 : ℚ) / 1000000000000) ≤ ((452243436273 : ℚ) / 1000000000000) + (22853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243438187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243436273 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22853:ℚ)^(-2:ℤ) : ℝ) = ((22853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2551 : ((((4522434401 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22853 < q → q < 22859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22859).mp (by decide +kernel))) hgap
  have hprev := s2L_2550
  have hrat : ((4522434401 : ℚ) / 10000000000) ≤ ((452243438187 : ℚ) / 1000000000000) + (22859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522434401 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452243438187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22859:ℚ)^(-2:ℤ) : ℝ) = ((22859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2552 : ((((452243442013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22859 < q → q < 22861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22861).mp (by decide +kernel))) hgap
  have hprev := s2L_2551
  have hrat : ((452243442013 : ℚ) / 1000000000000) ≤ ((4522434401 : ℚ) / 10000000000) + (22861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243442013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522434401 : ℚ) / 10000000000) : ℚ) : ℝ) + ((22861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22861:ℚ)^(-2:ℤ) : ℝ) = ((22861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2553 : ((((113060860981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22861 < q → q < 22871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22871).mp (by decide +kernel))) hgap
  have hprev := s2L_2552
  have hrat : ((113060860981 : ℚ) / 250000000000) ≤ ((452243442013 : ℚ) / 1000000000000) + (22871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060860981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243442013 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22871:ℚ)^(-2:ℤ) : ℝ) = ((22871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2554 : ((((226121722917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22871 < q → q < 22877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22877).mp (by decide +kernel))) hgap
  have hprev := s2L_2553
  have hrat : ((226121722917 : ℚ) / 500000000000) ≤ ((113060860981 : ℚ) / 250000000000) + (22877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121722917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060860981 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22877:ℚ)^(-2:ℤ) : ℝ) = ((22877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2555 : ((((22612172387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22877 < q → q < 22901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22901).mp (by decide +kernel))) hgap
  have hprev := s2L_2554
  have hrat : ((22612172387 : ℚ) / 50000000000) ≤ ((226121722917 : ℚ) / 500000000000) + (22901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612172387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121722917 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22901:ℚ)^(-2:ℤ) : ℝ) = ((22901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2556 : ((((90448689929 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22901 < q → q < 22907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22907).mp (by decide +kernel))) hgap
  have hprev := s2L_2555
  have hrat : ((90448689929 : ℚ) / 200000000000) ≤ ((22612172387 : ℚ) / 50000000000) + (22907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448689929 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612172387 : ℚ) / 50000000000) : ℚ) : ℝ) + ((22907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22907:ℚ)^(-2:ℤ) : ℝ) = ((22907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2557 : ((((113060862887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22907 < q → q < 22921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22921).mp (by decide +kernel))) hgap
  have hprev := s2L_2556
  have hrat : ((113060862887 : ℚ) / 250000000000) ≤ ((90448689929 : ℚ) / 200000000000) + (22921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060862887 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448689929 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22921:ℚ)^(-2:ℤ) : ℝ) = ((22921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2558 : ((((56530431681 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22921 < q → q < 22937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22937).mp (by decide +kernel))) hgap
  have hprev := s2L_2557
  have hrat : ((56530431681 : ℚ) / 125000000000) ≤ ((113060862887 : ℚ) / 250000000000) + (22937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530431681 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060862887 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22937:ℚ)^(-2:ℤ) : ℝ) = ((22937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2559 : ((((452243455347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22937 < q → q < 22943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22943).mp (by decide +kernel))) hgap
  have hprev := s2L_2558
  have hrat : ((452243455347 : ℚ) / 1000000000000) ≤ ((56530431681 : ℚ) / 125000000000) + (22943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243455347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530431681 : ℚ) / 125000000000) : ℚ) : ℝ) + ((22943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22943:ℚ)^(-2:ℤ) : ℝ) = ((22943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2560 : ((((452243457243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22943 < q → q < 22961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22961).mp (by decide +kernel))) hgap
  have hprev := s2L_2559
  have hrat : ((452243457243 : ℚ) / 1000000000000) ≤ ((452243455347 : ℚ) / 1000000000000) + (22961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243457243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243455347 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22961:ℚ)^(-2:ℤ) : ℝ) = ((22961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2561 : ((((452243459139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22961 < q → q < 22963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22963).mp (by decide +kernel))) hgap
  have hprev := s2L_2560
  have hrat : ((452243459139 : ℚ) / 1000000000000) ≤ ((452243457243 : ℚ) / 1000000000000) + (22963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243459139 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243457243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22963:ℚ)^(-2:ℤ) : ℝ) = ((22963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2562 : ((((452243461033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22963 < q → q < 22973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22973).mp (by decide +kernel))) hgap
  have hprev := s2L_2561
  have hrat : ((452243461033 : ℚ) / 1000000000000) ≤ ((452243459139 : ℚ) / 1000000000000) + (22973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243461033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243459139 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22973:ℚ)^(-2:ℤ) : ℝ) = ((22973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2563 : ((((113060865731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22973 < q → q < 22993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22993).mp (by decide +kernel))) hgap
  have hprev := s2L_2562
  have hrat : ((113060865731 : ℚ) / 250000000000) ≤ ((452243461033 : ℚ) / 1000000000000) + (22993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060865731 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243461033 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22993:ℚ)^(-2:ℤ) : ℝ) = ((22993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2564 : ((((452243464813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22993 < q → q < 23003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23003).mp (by decide +kernel))) hgap
  have hprev := s2L_2563
  have hrat : ((452243464813 : ℚ) / 1000000000000) ≤ ((113060865731 : ℚ) / 250000000000) + (23003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243464813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060865731 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23003:ℚ)^(-2:ℤ) : ℝ) = ((23003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2565 : ((((452243466701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23003 < q → q < 23011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23011).mp (by decide +kernel))) hgap
  have hprev := s2L_2564
  have hrat : ((452243466701 : ℚ) / 1000000000000) ≤ ((452243464813 : ℚ) / 1000000000000) + (23011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243466701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243464813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23011:ℚ)^(-2:ℤ) : ℝ) = ((23011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2566 : ((((113060867147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23011 < q → q < 23017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23017).mp (by decide +kernel))) hgap
  have hprev := s2L_2565
  have hrat : ((113060867147 : ℚ) / 250000000000) ≤ ((452243466701 : ℚ) / 1000000000000) + (23017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060867147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243466701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23017:ℚ)^(-2:ℤ) : ℝ) = ((23017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2567 : ((((226121735237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23017 < q → q < 23021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23021).mp (by decide +kernel))) hgap
  have hprev := s2L_2566
  have hrat : ((226121735237 : ℚ) / 500000000000) ≤ ((113060867147 : ℚ) / 250000000000) + (23021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121735237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060867147 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23021:ℚ)^(-2:ℤ) : ℝ) = ((23021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2568 : ((((452243472359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23021 < q → q < 23027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23027).mp (by decide +kernel))) hgap
  have hprev := s2L_2567
  have hrat : ((452243472359 : ℚ) / 1000000000000) ≤ ((226121735237 : ℚ) / 500000000000) + (23027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243472359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121735237 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23027:ℚ)^(-2:ℤ) : ℝ) = ((23027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2569 : ((((113060868561 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23027 < q → q < 23029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23029).mp (by decide +kernel))) hgap
  have hprev := s2L_2568
  have hrat : ((113060868561 : ℚ) / 250000000000) ≤ ((452243472359 : ℚ) / 1000000000000) + (23029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060868561 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243472359 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23029:ℚ)^(-2:ℤ) : ℝ) = ((23029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2570 : ((((452243476127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23029 < q → q < 23039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23039).mp (by decide +kernel))) hgap
  have hprev := s2L_2569
  have hrat : ((452243476127 : ℚ) / 1000000000000) ≤ ((113060868561 : ℚ) / 250000000000) + (23039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243476127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060868561 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23039:ℚ)^(-2:ℤ) : ℝ) = ((23039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2571 : ((((45224347801 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23039 < q → q < 23041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23041).mp (by decide +kernel))) hgap
  have hprev := s2L_2570
  have hrat : ((45224347801 : ℚ) / 100000000000) ≤ ((452243476127 : ℚ) / 1000000000000) + (23041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224347801 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243476127 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23041:ℚ)^(-2:ℤ) : ℝ) = ((23041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2572 : ((((452243479891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23041 < q → q < 23053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23053).mp (by decide +kernel))) hgap
  have hprev := s2L_2571
  have hrat : ((452243479891 : ℚ) / 1000000000000) ≤ ((45224347801 : ℚ) / 100000000000) + (23053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243479891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224347801 : ℚ) / 100000000000) : ℚ) : ℝ) + ((23053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23053:ℚ)^(-2:ℤ) : ℝ) = ((23053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2573 : ((((113060870443 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23053 < q → q < 23057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23057).mp (by decide +kernel))) hgap
  have hprev := s2L_2572
  have hrat : ((113060870443 : ℚ) / 250000000000) ≤ ((452243479891 : ℚ) / 1000000000000) + (23057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060870443 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243479891 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23057:ℚ)^(-2:ℤ) : ℝ) = ((23057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2574 : ((((113060870913 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23057 < q → q < 23059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23059).mp (by decide +kernel))) hgap
  have hprev := s2L_2573
  have hrat : ((113060870913 : ℚ) / 250000000000) ≤ ((113060870443 : ℚ) / 250000000000) + (23059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060870913 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060870443 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23059:ℚ)^(-2:ℤ) : ℝ) = ((23059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2575 : ((((113060871383 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23059 < q → q < 23063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23063).mp (by decide +kernel))) hgap
  have hprev := s2L_2574
  have hrat : ((113060871383 : ℚ) / 250000000000) ≤ ((113060870913 : ℚ) / 250000000000) + (23063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060871383 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060870913 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23063:ℚ)^(-2:ℤ) : ℝ) = ((23063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2576 : ((((45224348741 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23063 < q → q < 23071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23071).mp (by decide +kernel))) hgap
  have hprev := s2L_2575
  have hrat : ((45224348741 : ℚ) / 100000000000) ≤ ((113060871383 : ℚ) / 250000000000) + (23071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224348741 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060871383 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23071:ℚ)^(-2:ℤ) : ℝ) = ((23071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2577 : ((((452243489287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23071 < q → q < 23081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23081).mp (by decide +kernel))) hgap
  have hprev := s2L_2576
  have hrat : ((452243489287 : ℚ) / 1000000000000) ≤ ((45224348741 : ℚ) / 100000000000) + (23081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243489287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224348741 : ℚ) / 100000000000) : ℚ) : ℝ) + ((23081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23081:ℚ)^(-2:ℤ) : ℝ) = ((23081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2578 : ((((452243491163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23081 < q → q < 23087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23087).mp (by decide +kernel))) hgap
  have hprev := s2L_2577
  have hrat : ((452243491163 : ℚ) / 1000000000000) ≤ ((452243489287 : ℚ) / 1000000000000) + (23087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243491163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243489287 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23087:ℚ)^(-2:ℤ) : ℝ) = ((23087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2579 : ((((452243493037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23087 < q → q < 23099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23099).mp (by decide +kernel))) hgap
  have hprev := s2L_2578
  have hrat : ((452243493037 : ℚ) / 1000000000000) ≤ ((452243491163 : ℚ) / 1000000000000) + (23099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243493037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243491163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23099:ℚ)^(-2:ℤ) : ℝ) = ((23099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2580 : ((((113060873727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23099 < q → q < 23117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23117).mp (by decide +kernel))) hgap
  have hprev := s2L_2579
  have hrat : ((113060873727 : ℚ) / 250000000000) ≤ ((452243493037 : ℚ) / 1000000000000) + (23117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060873727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243493037 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23117:ℚ)^(-2:ℤ) : ℝ) = ((23117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2581 : ((((452243496777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23117 < q → q < 23131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23131).mp (by decide +kernel))) hgap
  have hprev := s2L_2580
  have hrat : ((452243496777 : ℚ) / 1000000000000) ≤ ((113060873727 : ℚ) / 250000000000) + (23131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243496777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060873727 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23131:ℚ)^(-2:ℤ) : ℝ) = ((23131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2582 : ((((113060874661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23131 < q → q < 23143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23143).mp (by decide +kernel))) hgap
  have hprev := s2L_2581
  have hrat : ((113060874661 : ℚ) / 250000000000) ≤ ((452243496777 : ℚ) / 1000000000000) + (23143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060874661 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243496777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23143:ℚ)^(-2:ℤ) : ℝ) = ((23143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2583 : ((((113060875127 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23143 < q → q < 23159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23159).mp (by decide +kernel))) hgap
  have hprev := s2L_2582
  have hrat : ((113060875127 : ℚ) / 250000000000) ≤ ((113060874661 : ℚ) / 250000000000) + (23159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060875127 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060874661 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23159:ℚ)^(-2:ℤ) : ℝ) = ((23159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2584 : ((((452243502371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23159 < q → q < 23167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23167).mp (by decide +kernel))) hgap
  have hprev := s2L_2583
  have hrat : ((452243502371 : ℚ) / 1000000000000) ≤ ((113060875127 : ℚ) / 250000000000) + (23167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243502371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060875127 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23167:ℚ)^(-2:ℤ) : ℝ) = ((23167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2585 : ((((452243504233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23167 < q → q < 23173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23173).mp (by decide +kernel))) hgap
  have hprev := s2L_2584
  have hrat : ((452243504233 : ℚ) / 1000000000000) ≤ ((452243502371 : ℚ) / 1000000000000) + (23173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243504233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243502371 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23173:ℚ)^(-2:ℤ) : ℝ) = ((23173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2586 : ((((113060876523 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23173 < q → q < 23189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23189).mp (by decide +kernel))) hgap
  have hprev := s2L_2585
  have hrat : ((113060876523 : ℚ) / 250000000000) ≤ ((452243504233 : ℚ) / 1000000000000) + (23189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060876523 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243504233 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23189:ℚ)^(-2:ℤ) : ℝ) = ((23189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2587 : ((((9044870159 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23189 < q → q < 23197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23197).mp (by decide +kernel))) hgap
  have hprev := s2L_2586
  have hrat : ((9044870159 : ℚ) / 20000000000) ≤ ((113060876523 : ℚ) / 250000000000) + (23197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044870159 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((113060876523 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23197:ℚ)^(-2:ℤ) : ℝ) = ((23197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2588 : ((((452243509807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23197 < q → q < 23201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23201).mp (by decide +kernel))) hgap
  have hprev := s2L_2587
  have hrat : ((452243509807 : ℚ) / 1000000000000) ≤ ((9044870159 : ℚ) / 20000000000) + (23201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243509807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044870159 : ℚ) / 20000000000) : ℚ) : ℝ) + ((23201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23201:ℚ)^(-2:ℤ) : ℝ) = ((23201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2589 : ((((28265219479 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23201 < q → q < 23203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23203).mp (by decide +kernel))) hgap
  have hprev := s2L_2588
  have hrat : ((28265219479 : ℚ) / 62500000000) ≤ ((452243509807 : ℚ) / 1000000000000) + (23203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265219479 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452243509807 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23203:ℚ)^(-2:ℤ) : ℝ) = ((23203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2590 : ((((5653043919 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23203 < q → q < 23209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23209).mp (by decide +kernel))) hgap
  have hprev := s2L_2589
  have hrat : ((5653043919 : ℚ) / 12500000000) ≤ ((28265219479 : ℚ) / 62500000000) + (23209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653043919 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((28265219479 : ℚ) / 62500000000) : ℚ) : ℝ) + ((23209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23209:ℚ)^(-2:ℤ) : ℝ) = ((23209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2591 : ((((452243515373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23209 < q → q < 23227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23227).mp (by decide +kernel))) hgap
  have hprev := s2L_2590
  have hrat : ((452243515373 : ℚ) / 1000000000000) ≤ ((5653043919 : ℚ) / 12500000000) + (23227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243515373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653043919 : ℚ) / 12500000000) : ℚ) : ℝ) + ((23227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23227:ℚ)^(-2:ℤ) : ℝ) = ((23227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2592 : ((((226121758611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23227 < q → q < 23251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23251).mp (by decide +kernel))) hgap
  have hprev := s2L_2591
  have hrat : ((226121758611 : ℚ) / 500000000000) ≤ ((452243515373 : ℚ) / 1000000000000) + (23251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121758611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243515373 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23251:ℚ)^(-2:ℤ) : ℝ) = ((23251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2593 : ((((113060879767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23251 < q → q < 23269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23269).mp (by decide +kernel))) hgap
  have hprev := s2L_2592
  have hrat : ((113060879767 : ℚ) / 250000000000) ≤ ((226121758611 : ℚ) / 500000000000) + (23269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060879767 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121758611 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23269:ℚ)^(-2:ℤ) : ℝ) = ((23269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2594 : ((((452243520913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23269 < q → q < 23279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23279).mp (by decide +kernel))) hgap
  have hprev := s2L_2593
  have hrat : ((452243520913 : ℚ) / 1000000000000) ≤ ((113060879767 : ℚ) / 250000000000) + (23279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243520913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060879767 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23279:ℚ)^(-2:ℤ) : ℝ) = ((23279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2595 : ((((113060880689 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23279 < q → q < 23291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23291).mp (by decide +kernel))) hgap
  have hprev := s2L_2594
  have hrat : ((113060880689 : ℚ) / 250000000000) ≤ ((452243520913 : ℚ) / 1000000000000) + (23291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060880689 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243520913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23291:ℚ)^(-2:ℤ) : ℝ) = ((23291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2596 : ((((452243524599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23291 < q → q < 23293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23293).mp (by decide +kernel))) hgap
  have hprev := s2L_2595
  have hrat : ((452243524599 : ℚ) / 1000000000000) ≤ ((113060880689 : ℚ) / 250000000000) + (23293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243524599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060880689 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23293:ℚ)^(-2:ℤ) : ℝ) = ((23293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2597 : ((((452243526441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23293 < q → q < 23297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23297).mp (by decide +kernel))) hgap
  have hprev := s2L_2596
  have hrat : ((452243526441 : ℚ) / 1000000000000) ≤ ((452243524599 : ℚ) / 1000000000000) + (23297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243526441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243524599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23297:ℚ)^(-2:ℤ) : ℝ) = ((23297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2598 : ((((452243528281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23297 < q → q < 23311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23311).mp (by decide +kernel))) hgap
  have hprev := s2L_2597
  have hrat : ((452243528281 : ℚ) / 1000000000000) ≤ ((452243526441 : ℚ) / 1000000000000) + (23311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243528281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243526441 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23311:ℚ)^(-2:ℤ) : ℝ) = ((23311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2599 : ((((452243530119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23311 < q → q < 23321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23321).mp (by decide +kernel))) hgap
  have hprev := s2L_2598
  have hrat : ((452243530119 : ℚ) / 1000000000000) ≤ ((452243528281 : ℚ) / 1000000000000) + (23321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243530119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243528281 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23321:ℚ)^(-2:ℤ) : ℝ) = ((23321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2600 : ((((113060882989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23321 < q → q < 23327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23327).mp (by decide +kernel))) hgap
  have hprev := s2L_2599
  have hrat : ((113060882989 : ℚ) / 250000000000) ≤ ((452243530119 : ℚ) / 1000000000000) + (23327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060882989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243530119 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23327:ℚ)^(-2:ℤ) : ℝ) = ((23327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2601 : ((((14132610431 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23327 < q → q < 23333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23333).mp (by decide +kernel))) hgap
  have hprev := s2L_2600
  have hrat : ((14132610431 : ℚ) / 31250000000) ≤ ((113060882989 : ℚ) / 250000000000) + (23333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132610431 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113060882989 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23333:ℚ)^(-2:ℤ) : ℝ) = ((23333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2602 : ((((452243535627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23333 < q → q < 23339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23339).mp (by decide +kernel))) hgap
  have hprev := s2L_2601
  have hrat : ((452243535627 : ℚ) / 1000000000000) ≤ ((14132610431 : ℚ) / 31250000000) + (23339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243535627 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132610431 : ℚ) / 31250000000) : ℚ) : ℝ) + ((23339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23339:ℚ)^(-2:ℤ) : ℝ) = ((23339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2603 : ((((22612176873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23339 < q → q < 23357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23357).mp (by decide +kernel))) hgap
  have hprev := s2L_2602
  have hrat : ((22612176873 : ℚ) / 50000000000) ≤ ((452243535627 : ℚ) / 1000000000000) + (23357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612176873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243535627 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23357:ℚ)^(-2:ℤ) : ℝ) = ((23357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2604 : ((((452243539291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23357 < q → q < 23369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23369).mp (by decide +kernel))) hgap
  have hprev := s2L_2603
  have hrat : ((452243539291 : ℚ) / 1000000000000) ≤ ((22612176873 : ℚ) / 50000000000) + (23369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243539291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612176873 : ℚ) / 50000000000) : ℚ) : ℝ) + ((23369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23369:ℚ)^(-2:ℤ) : ℝ) = ((23369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2605 : ((((452243541121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23369 < q → q < 23371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23371).mp (by decide +kernel))) hgap
  have hprev := s2L_2604
  have hrat : ((452243541121 : ℚ) / 1000000000000) ≤ ((452243539291 : ℚ) / 1000000000000) + (23371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243541121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243539291 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23371:ℚ)^(-2:ℤ) : ℝ) = ((23371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2606 : ((((452243542947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23371 < q → q < 23399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23399).mp (by decide +kernel))) hgap
  have hprev := s2L_2605
  have hrat : ((452243542947 : ℚ) / 1000000000000) ≤ ((452243541121 : ℚ) / 1000000000000) + (23399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243542947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243541121 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23399:ℚ)^(-2:ℤ) : ℝ) = ((23399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2607 : ((((45224354477 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23399 < q → q < 23417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23417).mp (by decide +kernel))) hgap
  have hprev := s2L_2606
  have hrat : ((45224354477 : ℚ) / 100000000000) ≤ ((452243542947 : ℚ) / 1000000000000) + (23417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224354477 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243542947 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23417:ℚ)^(-2:ℤ) : ℝ) = ((23417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2608 : ((((452243546591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23417 < q → q < 23431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23431).mp (by decide +kernel))) hgap
  have hprev := s2L_2607
  have hrat : ((452243546591 : ℚ) / 1000000000000) ≤ ((45224354477 : ℚ) / 100000000000) + (23431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243546591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224354477 : ℚ) / 100000000000) : ℚ) : ℝ) + ((23431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23431:ℚ)^(-2:ℤ) : ℝ) = ((23431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2609 : ((((452243548409 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23431 < q → q < 23447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23447).mp (by decide +kernel))) hgap
  have hprev := s2L_2608
  have hrat : ((452243548409 : ℚ) / 1000000000000) ≤ ((452243546591 : ℚ) / 1000000000000) + (23447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243548409 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243546591 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23447:ℚ)^(-2:ℤ) : ℝ) = ((23447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2610 : ((((226121775113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23447 < q → q < 23459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23459).mp (by decide +kernel))) hgap
  have hprev := s2L_2609
  have hrat : ((226121775113 : ℚ) / 500000000000) ≤ ((452243548409 : ℚ) / 1000000000000) + (23459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121775113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243548409 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23459:ℚ)^(-2:ℤ) : ℝ) = ((23459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2611 : ((((11306088801 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23459 < q → q < 23473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23473).mp (by decide +kernel))) hgap
  have hprev := s2L_2610
  have hrat : ((11306088801 : ℚ) / 25000000000) ≤ ((226121775113 : ℚ) / 500000000000) + (23473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306088801 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226121775113 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23473:ℚ)^(-2:ℤ) : ℝ) = ((23473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2612 : ((((452243553851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23473 < q → q < 23497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23497).mp (by decide +kernel))) hgap
  have hprev := s2L_2611
  have hrat : ((452243553851 : ℚ) / 1000000000000) ≤ ((11306088801 : ℚ) / 25000000000) + (23497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243553851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306088801 : ℚ) / 25000000000) : ℚ) : ℝ) + ((23497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23497:ℚ)^(-2:ℤ) : ℝ) = ((23497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2613 : ((((22612177783 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23497 < q → q < 23509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23509).mp (by decide +kernel))) hgap
  have hprev := s2L_2612
  have hrat : ((22612177783 : ℚ) / 50000000000) ≤ ((452243553851 : ℚ) / 1000000000000) + (23509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612177783 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243553851 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23509:ℚ)^(-2:ℤ) : ℝ) = ((23509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2614 : ((((226121778733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23509 < q → q < 23531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23531).mp (by decide +kernel))) hgap
  have hprev := s2L_2613
  have hrat : ((226121778733 : ℚ) / 500000000000) ≤ ((22612177783 : ℚ) / 50000000000) + (23531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121778733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612177783 : ℚ) / 50000000000) : ℚ) : ℝ) + ((23531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23531:ℚ)^(-2:ℤ) : ℝ) = ((23531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2615 : ((((452243559271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23531 < q → q < 23537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23537).mp (by decide +kernel))) hgap
  have hprev := s2L_2614
  have hrat : ((452243559271 : ℚ) / 1000000000000) ≤ ((226121778733 : ℚ) / 500000000000) + (23537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243559271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121778733 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23537:ℚ)^(-2:ℤ) : ℝ) = ((23537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2616 : ((((18089742443 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23537 < q → q < 23539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23539).mp (by decide +kernel))) hgap
  have hprev := s2L_2615
  have hrat : ((18089742443 : ℚ) / 40000000000) ≤ ((452243559271 : ℚ) / 1000000000000) + (23539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089742443 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452243559271 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23539:ℚ)^(-2:ℤ) : ℝ) = ((23539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2617 : ((((226121781439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23539 < q → q < 23549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23549).mp (by decide +kernel))) hgap
  have hprev := s2L_2616
  have hrat : ((226121781439 : ℚ) / 500000000000) ≤ ((18089742443 : ℚ) / 40000000000) + (23549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121781439 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089742443 : ℚ) / 40000000000) : ℚ) : ℝ) + ((23549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23549:ℚ)^(-2:ℤ) : ℝ) = ((23549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2618 : ((((11306089117 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23549 < q → q < 23557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23557).mp (by decide +kernel))) hgap
  have hprev := s2L_2617
  have hrat : ((11306089117 : ℚ) / 25000000000) ≤ ((226121781439 : ℚ) / 500000000000) + (23557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306089117 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226121781439 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23557:ℚ)^(-2:ℤ) : ℝ) = ((23557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2619 : ((((452243566481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23557 < q → q < 23561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23561).mp (by decide +kernel))) hgap
  have hprev := s2L_2618
  have hrat : ((452243566481 : ℚ) / 1000000000000) ≤ ((11306089117 : ℚ) / 25000000000) + (23561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243566481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306089117 : ℚ) / 25000000000) : ℚ) : ℝ) + ((23561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23561:ℚ)^(-2:ℤ) : ℝ) = ((23561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2620 : ((((226121784141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23561 < q → q < 23563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23563).mp (by decide +kernel))) hgap
  have hprev := s2L_2619
  have hrat : ((226121784141 : ℚ) / 500000000000) ≤ ((452243566481 : ℚ) / 1000000000000) + (23563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121784141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243566481 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23563:ℚ)^(-2:ℤ) : ℝ) = ((23563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2621 : ((((226121785041 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23563 < q → q < 23567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23567).mp (by decide +kernel))) hgap
  have hprev := s2L_2620
  have hrat : ((226121785041 : ℚ) / 500000000000) ≤ ((226121784141 : ℚ) / 500000000000) + (23567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121785041 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121784141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23567:ℚ)^(-2:ℤ) : ℝ) = ((23567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2622 : ((((11306089297 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23567 < q → q < 23581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23581).mp (by decide +kernel))) hgap
  have hprev := s2L_2621
  have hrat : ((11306089297 : ℚ) / 25000000000) ≤ ((226121785041 : ℚ) / 500000000000) + (23581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306089297 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226121785041 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23581:ℚ)^(-2:ℤ) : ℝ) = ((23581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2623 : ((((113060893419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23581 < q → q < 23593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23593).mp (by decide +kernel))) hgap
  have hprev := s2L_2622
  have hrat : ((113060893419 : ℚ) / 250000000000) ≤ ((11306089297 : ℚ) / 25000000000) + (23593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060893419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11306089297 : ℚ) / 25000000000) : ℚ) : ℝ) + ((23593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23593:ℚ)^(-2:ℤ) : ℝ) = ((23593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2624 : ((((452243575471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23593 < q → q < 23599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23599).mp (by decide +kernel))) hgap
  have hprev := s2L_2623
  have hrat : ((452243575471 : ℚ) / 1000000000000) ≤ ((113060893419 : ℚ) / 250000000000) + (23599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243575471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060893419 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23599:ℚ)^(-2:ℤ) : ℝ) = ((23599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2625 : ((((226121788633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23599 < q → q < 23603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23603).mp (by decide +kernel))) hgap
  have hprev := s2L_2624
  have hrat : ((226121788633 : ℚ) / 500000000000) ≤ ((452243575471 : ℚ) / 1000000000000) + (23603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121788633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243575471 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23603:ℚ)^(-2:ℤ) : ℝ) = ((23603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2626 : ((((22612178953 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23603 < q → q < 23609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23609).mp (by decide +kernel))) hgap
  have hprev := s2L_2625
  have hrat : ((22612178953 : ℚ) / 50000000000) ≤ ((226121788633 : ℚ) / 500000000000) + (23609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612178953 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121788633 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23609:ℚ)^(-2:ℤ) : ℝ) = ((23609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2627 : ((((452243580851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23609 < q → q < 23623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23623).mp (by decide +kernel))) hgap
  have hprev := s2L_2626
  have hrat : ((452243580851 : ℚ) / 1000000000000) ≤ ((22612178953 : ℚ) / 50000000000) + (23623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243580851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612178953 : ℚ) / 50000000000) : ℚ) : ℝ) + ((23623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23623:ℚ)^(-2:ℤ) : ℝ) = ((23623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2628 : ((((226121791321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23623 < q → q < 23627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23627).mp (by decide +kernel))) hgap
  have hprev := s2L_2627
  have hrat : ((226121791321 : ℚ) / 500000000000) ≤ ((452243580851 : ℚ) / 1000000000000) + (23627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121791321 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243580851 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23627:ℚ)^(-2:ℤ) : ℝ) = ((23627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2629 : ((((452243584433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23627 < q → q < 23629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23629).mp (by decide +kernel))) hgap
  have hprev := s2L_2628
  have hrat : ((452243584433 : ℚ) / 1000000000000) ≤ ((226121791321 : ℚ) / 500000000000) + (23629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243584433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121791321 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23629:ℚ)^(-2:ℤ) : ℝ) = ((23629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2630 : ((((452243586223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23629 < q → q < 23633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23633).mp (by decide +kernel))) hgap
  have hprev := s2L_2629
  have hrat : ((452243586223 : ℚ) / 1000000000000) ≤ ((452243584433 : ℚ) / 1000000000000) + (23633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243586223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243584433 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23633:ℚ)^(-2:ℤ) : ℝ) = ((23633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2631 : ((((56530448501 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23633 < q → q < 23663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23663).mp (by decide +kernel))) hgap
  have hprev := s2L_2630
  have hrat : ((56530448501 : ℚ) / 125000000000) ≤ ((452243586223 : ℚ) / 1000000000000) + (23663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530448501 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243586223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23663:ℚ)^(-2:ℤ) : ℝ) = ((23663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2632 : ((((452243589793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23663 < q → q < 23669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23669).mp (by decide +kernel))) hgap
  have hprev := s2L_2631
  have hrat : ((452243589793 : ℚ) / 1000000000000) ≤ ((56530448501 : ℚ) / 125000000000) + (23669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243589793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530448501 : ℚ) / 125000000000) : ℚ) : ℝ) + ((23669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23669:ℚ)^(-2:ℤ) : ℝ) = ((23669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2633 : ((((452243591577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23669 < q → q < 23671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23671).mp (by decide +kernel))) hgap
  have hprev := s2L_2632
  have hrat : ((452243591577 : ℚ) / 1000000000000) ≤ ((452243589793 : ℚ) / 1000000000000) + (23671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243591577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243589793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23671:ℚ)^(-2:ℤ) : ℝ) = ((23671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2634 : ((((5653044917 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23671 < q → q < 23677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23677).mp (by decide +kernel))) hgap
  have hprev := s2L_2633
  have hrat : ((5653044917 : ℚ) / 12500000000) ≤ ((452243591577 : ℚ) / 1000000000000) + (23677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653044917 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((452243591577 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23677:ℚ)^(-2:ℤ) : ℝ) = ((23677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2635 : ((((226121797571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23677 < q → q < 23687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23687).mp (by decide +kernel))) hgap
  have hprev := s2L_2634
  have hrat : ((226121797571 : ℚ) / 500000000000) ≤ ((5653044917 : ℚ) / 12500000000) + (23687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121797571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5653044917 : ℚ) / 12500000000) : ℚ) : ℝ) + ((23687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23687:ℚ)^(-2:ℤ) : ℝ) = ((23687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2636 : ((((452243596923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23687 < q → q < 23689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23689).mp (by decide +kernel))) hgap
  have hprev := s2L_2635
  have hrat : ((452243596923 : ℚ) / 1000000000000) ≤ ((226121797571 : ℚ) / 500000000000) + (23689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243596923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121797571 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23689:ℚ)^(-2:ℤ) : ℝ) = ((23689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2637 : ((((4522435987 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23689 < q → q < 23719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23719).mp (by decide +kernel))) hgap
  have hprev := s2L_2636
  have hrat : ((4522435987 : ℚ) / 10000000000) ≤ ((452243596923 : ℚ) / 1000000000000) + (23719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522435987 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452243596923 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23719:ℚ)^(-2:ℤ) : ℝ) = ((23719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2638 : ((((226121800237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23719 < q → q < 23741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23741).mp (by decide +kernel))) hgap
  have hprev := s2L_2637
  have hrat : ((226121800237 : ℚ) / 500000000000) ≤ ((4522435987 : ℚ) / 10000000000) + (23741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121800237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522435987 : ℚ) / 10000000000) : ℚ) : ℝ) + ((23741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23741:ℚ)^(-2:ℤ) : ℝ) = ((23741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2639 : ((((452243602247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23741 < q → q < 23743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23743).mp (by decide +kernel))) hgap
  have hprev := s2L_2638
  have hrat : ((452243602247 : ℚ) / 1000000000000) ≤ ((226121800237 : ℚ) / 500000000000) + (23743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243602247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121800237 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23743:ℚ)^(-2:ℤ) : ℝ) = ((23743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2640 : ((((22612180201 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23743 < q → q < 23747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23747).mp (by decide +kernel))) hgap
  have hprev := s2L_2639
  have hrat : ((22612180201 : ℚ) / 50000000000) ≤ ((452243602247 : ℚ) / 1000000000000) + (23747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612180201 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243602247 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23747:ℚ)^(-2:ℤ) : ℝ) = ((23747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2641 : ((((14132612681 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23747 < q → q < 23753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23753).mp (by decide +kernel))) hgap
  have hprev := s2L_2640
  have hrat : ((14132612681 : ℚ) / 31250000000) ≤ ((22612180201 : ℚ) / 50000000000) + (23753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132612681 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((22612180201 : ℚ) / 50000000000) : ℚ) : ℝ) + ((23753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23753:ℚ)^(-2:ℤ) : ℝ) = ((23753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2642 : ((((452243607563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23753 < q → q < 23761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23761).mp (by decide +kernel))) hgap
  have hprev := s2L_2641
  have hrat : ((452243607563 : ℚ) / 1000000000000) ≤ ((14132612681 : ℚ) / 31250000000) + (23761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243607563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132612681 : ℚ) / 31250000000) : ℚ) : ℝ) + ((23761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23761:ℚ)^(-2:ℤ) : ℝ) = ((23761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2643 : ((((452243609333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23761 < q → q < 23767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23767).mp (by decide +kernel))) hgap
  have hprev := s2L_2642
  have hrat : ((452243609333 : ℚ) / 1000000000000) ≤ ((452243607563 : ℚ) / 1000000000000) + (23767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243609333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243607563 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23767:ℚ)^(-2:ℤ) : ℝ) = ((23767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2644 : ((((226121805551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23767 < q → q < 23773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23773).mp (by decide +kernel))) hgap
  have hprev := s2L_2643
  have hrat : ((226121805551 : ℚ) / 500000000000) ≤ ((452243609333 : ℚ) / 1000000000000) + (23773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121805551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243609333 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23773:ℚ)^(-2:ℤ) : ℝ) = ((23773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2645 : ((((452243612869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23773 < q → q < 23789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23789).mp (by decide +kernel))) hgap
  have hprev := s2L_2644
  have hrat : ((452243612869 : ℚ) / 1000000000000) ≤ ((226121805551 : ℚ) / 500000000000) + (23789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243612869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121805551 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23789:ℚ)^(-2:ℤ) : ℝ) = ((23789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2646 : ((((226121807317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23789 < q → q < 23801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23801).mp (by decide +kernel))) hgap
  have hprev := s2L_2645
  have hrat : ((226121807317 : ℚ) / 500000000000) ≤ ((452243612869 : ℚ) / 1000000000000) + (23801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121807317 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243612869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23801:ℚ)^(-2:ℤ) : ℝ) = ((23801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2647 : ((((452243616397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23801 < q → q < 23813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23813).mp (by decide +kernel))) hgap
  have hprev := s2L_2646
  have hrat : ((452243616397 : ℚ) / 1000000000000) ≤ ((226121807317 : ℚ) / 500000000000) + (23813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243616397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121807317 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23813:ℚ)^(-2:ℤ) : ℝ) = ((23813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2648 : ((((452243618159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23813 < q → q < 23819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23819).mp (by decide +kernel))) hgap
  have hprev := s2L_2647
  have hrat : ((452243618159 : ℚ) / 1000000000000) ≤ ((452243616397 : ℚ) / 1000000000000) + (23819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243618159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243616397 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23819:ℚ)^(-2:ℤ) : ℝ) = ((23819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2649 : ((((5653045249 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23819 < q → q < 23827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23827).mp (by decide +kernel))) hgap
  have hprev := s2L_2648
  have hrat : ((5653045249 : ℚ) / 12500000000) ≤ ((452243618159 : ℚ) / 1000000000000) + (23827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653045249 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((452243618159 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23827:ℚ)^(-2:ℤ) : ℝ) = ((23827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2650 : ((((5653045271 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23827 < q → q < 23831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23831).mp (by decide +kernel))) hgap
  have hprev := s2L_2649
  have hrat : ((5653045271 : ℚ) / 12500000000) ≤ ((5653045249 : ℚ) / 12500000000) + (23831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653045271 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((5653045249 : ℚ) / 12500000000) : ℚ) : ℝ) + ((23831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23831:ℚ)^(-2:ℤ) : ℝ) = ((23831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2651 : ((((5653045293 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23831 < q → q < 23833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23833).mp (by decide +kernel))) hgap
  have hprev := s2L_2650
  have hrat : ((5653045293 : ℚ) / 12500000000) ≤ ((5653045271 : ℚ) / 12500000000) + (23833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653045293 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((5653045271 : ℚ) / 12500000000) : ℚ) : ℝ) + ((23833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23833:ℚ)^(-2:ℤ) : ℝ) = ((23833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2652 : ((((113060906299 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23833 < q → q < 23857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23857).mp (by decide +kernel))) hgap
  have hprev := s2L_2651
  have hrat : ((113060906299 : ℚ) / 250000000000) ≤ ((5653045293 : ℚ) / 12500000000) + (23857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060906299 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5653045293 : ℚ) / 12500000000) : ℚ) : ℝ) + ((23857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23857:ℚ)^(-2:ℤ) : ℝ) = ((23857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2653 : ((((452243626951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23869, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23857 < q → q < 23869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23869).mp (by decide +kernel))) hgap
  have hprev := s2L_2652
  have hrat : ((452243626951 : ℚ) / 1000000000000) ≤ ((113060906299 : ℚ) / 250000000000) + (23869:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243626951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060906299 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23869:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23869:ℚ)^(-2:ℤ) : ℝ) = ((23869:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2654 : ((((90448725741 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23869 < q → q < 23873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23873).mp (by decide +kernel))) hgap
  have hprev := s2L_2653
  have hrat : ((90448725741 : ℚ) / 200000000000) ≤ ((452243626951 : ℚ) / 1000000000000) + (23873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448725741 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243626951 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23873:ℚ)^(-2:ℤ) : ℝ) = ((23873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2655 : ((((226121815229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23873 < q → q < 23879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23879).mp (by decide +kernel))) hgap
  have hprev := s2L_2654
  have hrat : ((226121815229 : ℚ) / 500000000000) ≤ ((90448725741 : ℚ) / 200000000000) + (23879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121815229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448725741 : ℚ) / 200000000000) : ℚ) : ℝ) + ((23879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23879:ℚ)^(-2:ℤ) : ℝ) = ((23879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2656 : ((((45224363221 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23879 < q → q < 23887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23887).mp (by decide +kernel))) hgap
  have hprev := s2L_2655
  have hrat : ((45224363221 : ℚ) / 100000000000) ≤ ((226121815229 : ℚ) / 500000000000) + (23887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224363221 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121815229 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23887:ℚ)^(-2:ℤ) : ℝ) = ((23887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2657 : ((((452243633961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23887 < q → q < 23893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23893).mp (by decide +kernel))) hgap
  have hprev := s2L_2656
  have hrat : ((452243633961 : ℚ) / 1000000000000) ≤ ((45224363221 : ℚ) / 100000000000) + (23893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243633961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224363221 : ℚ) / 100000000000) : ℚ) : ℝ) + ((23893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23893:ℚ)^(-2:ℤ) : ℝ) = ((23893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2658 : ((((452243635711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23899, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23893 < q → q < 23899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23899).mp (by decide +kernel))) hgap
  have hprev := s2L_2657
  have hrat : ((452243635711 : ℚ) / 1000000000000) ≤ ((452243633961 : ℚ) / 1000000000000) + (23899:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243635711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243633961 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23899:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23899:ℚ)^(-2:ℤ) : ℝ) = ((23899:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2659 : ((((22612181873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23899 < q → q < 23909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23909).mp (by decide +kernel))) hgap
  have hprev := s2L_2658
  have hrat : ((22612181873 : ℚ) / 50000000000) ≤ ((452243635711 : ℚ) / 1000000000000) + (23909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612181873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243635711 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23909:ℚ)^(-2:ℤ) : ℝ) = ((23909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2660 : ((((452243639209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23909 < q → q < 23911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23911).mp (by decide +kernel))) hgap
  have hprev := s2L_2659
  have hrat : ((452243639209 : ℚ) / 1000000000000) ≤ ((22612181873 : ℚ) / 50000000000) + (23911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243639209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612181873 : ℚ) / 50000000000) : ℚ) : ℝ) + ((23911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23911:ℚ)^(-2:ℤ) : ℝ) = ((23911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2661 : ((((452243640957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23911 < q → q < 23917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23917).mp (by decide +kernel))) hgap
  have hprev := s2L_2660
  have hrat : ((452243640957 : ℚ) / 1000000000000) ≤ ((452243639209 : ℚ) / 1000000000000) + (23917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243640957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243639209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23917:ℚ)^(-2:ℤ) : ℝ) = ((23917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2662 : ((((452243642703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23917 < q → q < 23929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23929).mp (by decide +kernel))) hgap
  have hprev := s2L_2661
  have hrat : ((452243642703 : ℚ) / 1000000000000) ≤ ((452243640957 : ℚ) / 1000000000000) + (23929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243642703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243640957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23929:ℚ)^(-2:ℤ) : ℝ) = ((23929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2663 : ((((90448728889 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23929 < q → q < 23957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23957).mp (by decide +kernel))) hgap
  have hprev := s2L_2662
  have hrat : ((90448728889 : ℚ) / 200000000000) ≤ ((452243642703 : ℚ) / 1000000000000) + (23957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448728889 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243642703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((23957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23957:ℚ)^(-2:ℤ) : ℝ) = ((23957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2664 : ((((90448729237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23957 < q → q < 23971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23971).mp (by decide +kernel))) hgap
  have hprev := s2L_2663
  have hrat : ((90448729237 : ℚ) / 200000000000) ≤ ((90448728889 : ℚ) / 200000000000) + (23971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448729237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448728889 : ℚ) / 200000000000) : ℚ) : ℝ) + ((23971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23971:ℚ)^(-2:ℤ) : ℝ) = ((23971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2665 : ((((113060911981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23971 < q → q < 23977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23977).mp (by decide +kernel))) hgap
  have hprev := s2L_2664
  have hrat : ((113060911981 : ℚ) / 250000000000) ≤ ((90448729237 : ℚ) / 200000000000) + (23977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060911981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448729237 : ℚ) / 200000000000) : ℚ) : ℝ) + ((23977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23977:ℚ)^(-2:ℤ) : ℝ) = ((23977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2666 : ((((226121824831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23977 < q → q < 23981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23981).mp (by decide +kernel))) hgap
  have hprev := s2L_2665
  have hrat : ((226121824831 : ℚ) / 500000000000) ≤ ((113060911981 : ℚ) / 250000000000) + (23981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121824831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060911981 : ℚ) / 250000000000) : ℚ) : ℝ) + ((23981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23981:ℚ)^(-2:ℤ) : ℝ) = ((23981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2667 : ((((452243651399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 23993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23981 < q → q < 23993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 23993).mp (by decide +kernel))) hgap
  have hprev := s2L_2666
  have hrat : ((452243651399 : ℚ) / 1000000000000) ≤ ((226121824831 : ℚ) / 500000000000) + (23993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243651399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121824831 : ℚ) / 500000000000) : ℚ) : ℝ) + ((23993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((23993:ℚ)^(-2:ℤ) : ℝ) = ((23993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2668 : ((((226121826567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 23993 < q → q < 24001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24001).mp (by decide +kernel))) hgap
  have hprev := s2L_2667
  have hrat : ((226121826567 : ℚ) / 500000000000) ≤ ((452243651399 : ℚ) / 1000000000000) + (24001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121826567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243651399 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24001:ℚ)^(-2:ℤ) : ℝ) = ((24001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2669 : ((((452243654869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24001 < q → q < 24007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24007).mp (by decide +kernel))) hgap
  have hprev := s2L_2668
  have hrat : ((452243654869 : ℚ) / 1000000000000) ≤ ((226121826567 : ℚ) / 500000000000) + (24007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243654869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121826567 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24007:ℚ)^(-2:ℤ) : ℝ) = ((24007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2670 : ((((226121828301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24007 < q → q < 24019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24019).mp (by decide +kernel))) hgap
  have hprev := s2L_2669
  have hrat : ((226121828301 : ℚ) / 500000000000) ≤ ((452243654869 : ℚ) / 1000000000000) + (24019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121828301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243654869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24019:ℚ)^(-2:ℤ) : ℝ) = ((24019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2671 : ((((226121829167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24019 < q → q < 24023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24023).mp (by decide +kernel))) hgap
  have hprev := s2L_2670
  have hrat : ((226121829167 : ℚ) / 500000000000) ≤ ((226121828301 : ℚ) / 500000000000) + (24023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121829167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121828301 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24023:ℚ)^(-2:ℤ) : ℝ) = ((24023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2672 : ((((90448732013 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24023 < q → q < 24029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24029).mp (by decide +kernel))) hgap
  have hprev := s2L_2671
  have hrat : ((90448732013 : ℚ) / 200000000000) ≤ ((226121829167 : ℚ) / 500000000000) + (24029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448732013 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121829167 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24029:ℚ)^(-2:ℤ) : ℝ) = ((24029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2673 : ((((226121830897 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24029 < q → q < 24043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24043).mp (by decide +kernel))) hgap
  have hprev := s2L_2672
  have hrat : ((226121830897 : ℚ) / 500000000000) ≤ ((90448732013 : ℚ) / 200000000000) + (24043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121830897 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448732013 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24043:ℚ)^(-2:ℤ) : ℝ) = ((24043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2674 : ((((452243663523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24043 < q → q < 24049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24049).mp (by decide +kernel))) hgap
  have hprev := s2L_2673
  have hrat : ((452243663523 : ℚ) / 1000000000000) ≤ ((226121830897 : ℚ) / 500000000000) + (24049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243663523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121830897 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24049:ℚ)^(-2:ℤ) : ℝ) = ((24049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2675 : ((((1808974661 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24049 < q → q < 24061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24061).mp (by decide +kernel))) hgap
  have hprev := s2L_2674
  have hrat : ((1808974661 : ℚ) / 4000000000) ≤ ((452243663523 : ℚ) / 1000000000000) + (24061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808974661 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((452243663523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24061:ℚ)^(-2:ℤ) : ℝ) = ((24061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2676 : ((((18089746679 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24061 < q → q < 24071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24071).mp (by decide +kernel))) hgap
  have hprev := s2L_2675
  have hrat : ((18089746679 : ℚ) / 40000000000) ≤ ((1808974661 : ℚ) / 4000000000) + (24071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089746679 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((1808974661 : ℚ) / 4000000000) : ℚ) : ℝ) + ((24071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24071:ℚ)^(-2:ℤ) : ℝ) = ((24071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2677 : ((((4522436687 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24071 < q → q < 24077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24077).mp (by decide +kernel))) hgap
  have hprev := s2L_2676
  have hrat : ((4522436687 : ℚ) / 10000000000) ≤ ((18089746679 : ℚ) / 40000000000) + (24077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522436687 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((18089746679 : ℚ) / 40000000000) : ℚ) : ℝ) + ((24077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24077:ℚ)^(-2:ℤ) : ℝ) = ((24077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2678 : ((((56530458803 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24077 < q → q < 24083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24083).mp (by decide +kernel))) hgap
  have hprev := s2L_2677
  have hrat : ((56530458803 : ℚ) / 125000000000) ≤ ((4522436687 : ℚ) / 10000000000) + (24083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530458803 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4522436687 : ℚ) / 10000000000) : ℚ) : ℝ) + ((24083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24083:ℚ)^(-2:ℤ) : ℝ) = ((24083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2679 : ((((452243672147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24083 < q → q < 24091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24091).mp (by decide +kernel))) hgap
  have hprev := s2L_2678
  have hrat : ((452243672147 : ℚ) / 1000000000000) ≤ ((56530458803 : ℚ) / 125000000000) + (24091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243672147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530458803 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24091:ℚ)^(-2:ℤ) : ℝ) = ((24091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2680 : ((((452243673869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24091 < q → q < 24097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24097).mp (by decide +kernel))) hgap
  have hprev := s2L_2679
  have hrat : ((452243673869 : ℚ) / 1000000000000) ≤ ((452243672147 : ℚ) / 1000000000000) + (24097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243673869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243672147 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24097:ℚ)^(-2:ℤ) : ℝ) = ((24097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2681 : ((((45224367559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24097 < q → q < 24103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24103).mp (by decide +kernel))) hgap
  have hprev := s2L_2680
  have hrat : ((45224367559 : ℚ) / 100000000000) ≤ ((452243673869 : ℚ) / 1000000000000) + (24103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224367559 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243673869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24103:ℚ)^(-2:ℤ) : ℝ) = ((24103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2682 : ((((45224367731 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24103 < q → q < 24107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24107).mp (by decide +kernel))) hgap
  have hprev := s2L_2681
  have hrat : ((45224367731 : ℚ) / 100000000000) ≤ ((45224367559 : ℚ) / 100000000000) + (24107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224367731 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((45224367559 : ℚ) / 100000000000) : ℚ) : ℝ) + ((24107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24107:ℚ)^(-2:ℤ) : ℝ) = ((24107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2683 : ((((45224367903 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24107 < q → q < 24109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24109).mp (by decide +kernel))) hgap
  have hprev := s2L_2682
  have hrat : ((45224367903 : ℚ) / 100000000000) ≤ ((45224367731 : ℚ) / 100000000000) + (24109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224367903 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((45224367731 : ℚ) / 100000000000) : ℚ) : ℝ) + ((24109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24109:ℚ)^(-2:ℤ) : ℝ) = ((24109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2684 : ((((452243680749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24109 < q → q < 24113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24113).mp (by decide +kernel))) hgap
  have hprev := s2L_2683
  have hrat : ((452243680749 : ℚ) / 1000000000000) ≤ ((45224367903 : ℚ) / 100000000000) + (24113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243680749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224367903 : ℚ) / 100000000000) : ℚ) : ℝ) + ((24113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24113:ℚ)^(-2:ℤ) : ℝ) = ((24113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2685 : ((((452243682467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24113 < q → q < 24121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24121).mp (by decide +kernel))) hgap
  have hprev := s2L_2684
  have hrat : ((452243682467 : ℚ) / 1000000000000) ≤ ((452243680749 : ℚ) / 1000000000000) + (24121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243682467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243680749 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24121:ℚ)^(-2:ℤ) : ℝ) = ((24121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2686 : ((((56530460523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24121 < q → q < 24133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24133).mp (by decide +kernel))) hgap
  have hprev := s2L_2685
  have hrat : ((56530460523 : ℚ) / 125000000000) ≤ ((452243682467 : ℚ) / 1000000000000) + (24133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530460523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243682467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24133:ℚ)^(-2:ℤ) : ℝ) = ((24133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2687 : ((((4522436859 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24133 < q → q < 24137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24137).mp (by decide +kernel))) hgap
  have hprev := s2L_2686
  have hrat : ((4522436859 : ℚ) / 10000000000) ≤ ((56530460523 : ℚ) / 125000000000) + (24137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522436859 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((56530460523 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24137:ℚ)^(-2:ℤ) : ℝ) = ((24137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2688 : ((((226121843807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24137 < q → q < 24151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24151).mp (by decide +kernel))) hgap
  have hprev := s2L_2687
  have hrat : ((226121843807 : ℚ) / 500000000000) ≤ ((4522436859 : ℚ) / 10000000000) + (24151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121843807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522436859 : ℚ) / 10000000000) : ℚ) : ℝ) + ((24151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24151:ℚ)^(-2:ℤ) : ℝ) = ((24151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2689 : ((((18089747573 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24151 < q → q < 24169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24169).mp (by decide +kernel))) hgap
  have hprev := s2L_2688
  have hrat : ((18089747573 : ℚ) / 40000000000) ≤ ((226121843807 : ℚ) / 500000000000) + (24169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089747573 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226121843807 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24169:ℚ)^(-2:ℤ) : ℝ) = ((24169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2690 : ((((90448738207 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24169 < q → q < 24179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24179).mp (by decide +kernel))) hgap
  have hprev := s2L_2689
  have hrat : ((90448738207 : ℚ) / 200000000000) ≤ ((18089747573 : ℚ) / 40000000000) + (24179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448738207 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089747573 : ℚ) / 40000000000) : ℚ) : ℝ) + ((24179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24179:ℚ)^(-2:ℤ) : ℝ) = ((24179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2691 : ((((90448738549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24179 < q → q < 24181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24181).mp (by decide +kernel))) hgap
  have hprev := s2L_2690
  have hrat : ((90448738549 : ℚ) / 200000000000) ≤ ((90448738207 : ℚ) / 200000000000) + (24181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448738549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448738207 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24181:ℚ)^(-2:ℤ) : ℝ) = ((24181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2692 : ((((113060923613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24181 < q → q < 24197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24197).mp (by decide +kernel))) hgap
  have hprev := s2L_2691
  have hrat : ((113060923613 : ℚ) / 250000000000) ≤ ((90448738549 : ℚ) / 200000000000) + (24197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060923613 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448738549 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24197:ℚ)^(-2:ℤ) : ℝ) = ((24197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2693 : ((((452243696159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24197 < q → q < 24203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24203).mp (by decide +kernel))) hgap
  have hprev := s2L_2692
  have hrat : ((452243696159 : ℚ) / 1000000000000) ≤ ((113060923613 : ℚ) / 250000000000) + (24203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243696159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060923613 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24203:ℚ)^(-2:ℤ) : ℝ) = ((24203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2694 : ((((452243697863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24203 < q → q < 24223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24223).mp (by decide +kernel))) hgap
  have hprev := s2L_2693
  have hrat : ((452243697863 : ℚ) / 1000000000000) ≤ ((452243696159 : ℚ) / 1000000000000) + (24223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243697863 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243696159 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24223:ℚ)^(-2:ℤ) : ℝ) = ((24223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2695 : ((((226121849783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24223 < q → q < 24229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24229).mp (by decide +kernel))) hgap
  have hprev := s2L_2694
  have hrat : ((226121849783 : ℚ) / 500000000000) ≤ ((452243697863 : ℚ) / 1000000000000) + (24229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121849783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243697863 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24229:ℚ)^(-2:ℤ) : ℝ) = ((24229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2696 : ((((113060925317 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24229 < q → q < 24239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24239).mp (by decide +kernel))) hgap
  have hprev := s2L_2695
  have hrat : ((113060925317 : ℚ) / 250000000000) ≤ ((226121849783 : ℚ) / 500000000000) + (24239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060925317 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121849783 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24239:ℚ)^(-2:ℤ) : ℝ) = ((24239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2697 : ((((56530462871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24239 < q → q < 24247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24247).mp (by decide +kernel))) hgap
  have hprev := s2L_2696
  have hrat : ((56530462871 : ℚ) / 125000000000) ≤ ((113060925317 : ℚ) / 250000000000) + (24247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530462871 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060925317 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24247:ℚ)^(-2:ℤ) : ℝ) = ((24247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2698 : ((((113060926167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24247 < q → q < 24251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24251).mp (by decide +kernel))) hgap
  have hprev := s2L_2697
  have hrat : ((113060926167 : ℚ) / 250000000000) ≤ ((56530462871 : ℚ) / 125000000000) + (24251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060926167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530462871 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24251:ℚ)^(-2:ℤ) : ℝ) = ((24251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2699 : ((((113060926591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24251 < q → q < 24281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24281).mp (by decide +kernel))) hgap
  have hprev := s2L_2698
  have hrat : ((113060926591 : ℚ) / 250000000000) ≤ ((113060926167 : ℚ) / 250000000000) + (24281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060926591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060926167 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24281:ℚ)^(-2:ℤ) : ℝ) = ((24281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2700 : ((((90448741611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24281 < q → q < 24317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24317).mp (by decide +kernel))) hgap
  have hprev := s2L_2699
  have hrat : ((90448741611 : ℚ) / 200000000000) ≤ ((113060926591 : ℚ) / 250000000000) + (24317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448741611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060926591 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24317:ℚ)^(-2:ℤ) : ℝ) = ((24317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2701 : ((((28265231859 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24317 < q → q < 24329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24329).mp (by decide +kernel))) hgap
  have hprev := s2L_2700
  have hrat : ((28265231859 : ℚ) / 62500000000) ≤ ((90448741611 : ℚ) / 200000000000) + (24329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265231859 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90448741611 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24329:ℚ)^(-2:ℤ) : ℝ) = ((24329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2702 : ((((56530463929 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24329 < q → q < 24337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24337).mp (by decide +kernel))) hgap
  have hprev := s2L_2701
  have hrat : ((56530463929 : ℚ) / 125000000000) ≤ ((28265231859 : ℚ) / 62500000000) + (24337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530463929 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28265231859 : ℚ) / 62500000000) : ℚ) : ℝ) + ((24337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24337:ℚ)^(-2:ℤ) : ℝ) = ((24337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2703 : ((((452243713117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24337 < q → q < 24359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24359).mp (by decide +kernel))) hgap
  have hprev := s2L_2702
  have hrat : ((452243713117 : ℚ) / 1000000000000) ≤ ((56530463929 : ℚ) / 125000000000) + (24359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243713117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530463929 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24359:ℚ)^(-2:ℤ) : ℝ) = ((24359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2704 : ((((1130609287 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24359 < q → q < 24371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24371).mp (by decide +kernel))) hgap
  have hprev := s2L_2703
  have hrat : ((1130609287 : ℚ) / 2500000000) ≤ ((452243713117 : ℚ) / 1000000000000) + (24371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1130609287 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((452243713117 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24371:ℚ)^(-2:ℤ) : ℝ) = ((24371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2705 : ((((452243716483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24371 < q → q < 24373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24373).mp (by decide +kernel))) hgap
  have hprev := s2L_2704
  have hrat : ((452243716483 : ℚ) / 1000000000000) ≤ ((1130609287 : ℚ) / 2500000000) + (24373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243716483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1130609287 : ℚ) / 2500000000) : ℚ) : ℝ) + ((24373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24373:ℚ)^(-2:ℤ) : ℝ) = ((24373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2706 : ((((90448743633 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24373 < q → q < 24379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24379).mp (by decide +kernel))) hgap
  have hprev := s2L_2705
  have hrat : ((90448743633 : ℚ) / 200000000000) ≤ ((452243716483 : ℚ) / 1000000000000) + (24379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448743633 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243716483 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24379:ℚ)^(-2:ℤ) : ℝ) = ((24379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2707 : ((((90448743969 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24379 < q → q < 24391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24391).mp (by decide +kernel))) hgap
  have hprev := s2L_2706
  have hrat : ((90448743969 : ℚ) / 200000000000) ≤ ((90448743633 : ℚ) / 200000000000) + (24391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448743969 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448743633 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24391:ℚ)^(-2:ℤ) : ℝ) = ((24391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2708 : ((((452243721523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24391 < q → q < 24407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24407).mp (by decide +kernel))) hgap
  have hprev := s2L_2707
  have hrat : ((452243721523 : ℚ) / 1000000000000) ≤ ((90448743969 : ℚ) / 200000000000) + (24407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243721523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448743969 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24407:ℚ)^(-2:ℤ) : ℝ) = ((24407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2709 : ((((282652327 : ℚ) / 625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24407 < q → q < 24413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24413).mp (by decide +kernel))) hgap
  have hprev := s2L_2708
  have hrat : ((282652327 : ℚ) / 625000000) ≤ ((452243721523 : ℚ) / 1000000000000) + (24413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((282652327 : ℚ) / 625000000) : ℚ) : ℝ) ≤ ((((452243721523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24413:ℚ)^(-2:ℤ) : ℝ) = ((24413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2710 : ((((452243724877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24413 < q → q < 24419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24419).mp (by decide +kernel))) hgap
  have hprev := s2L_2709
  have hrat : ((452243724877 : ℚ) / 1000000000000) ≤ ((282652327 : ℚ) / 625000000) + (24419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243724877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((282652327 : ℚ) / 625000000) : ℚ) : ℝ) + ((24419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24419:ℚ)^(-2:ℤ) : ℝ) = ((24419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2711 : ((((452243726553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24419 < q → q < 24421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24421).mp (by decide +kernel))) hgap
  have hprev := s2L_2710
  have hrat : ((452243726553 : ℚ) / 1000000000000) ≤ ((452243724877 : ℚ) / 1000000000000) + (24421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243726553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243724877 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24421:ℚ)^(-2:ℤ) : ℝ) = ((24421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2712 : ((((452243728227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24421 < q → q < 24439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24439).mp (by decide +kernel))) hgap
  have hprev := s2L_2711
  have hrat : ((452243728227 : ℚ) / 1000000000000) ≤ ((452243726553 : ℚ) / 1000000000000) + (24439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243728227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243726553 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24439:ℚ)^(-2:ℤ) : ℝ) = ((24439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2713 : ((((4522437299 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24439 < q → q < 24443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24443).mp (by decide +kernel))) hgap
  have hprev := s2L_2712
  have hrat : ((4522437299 : ℚ) / 10000000000) ≤ ((452243728227 : ℚ) / 1000000000000) + (24443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522437299 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452243728227 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24443:ℚ)^(-2:ℤ) : ℝ) = ((24443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2714 : ((((45224373157 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24443 < q → q < 24469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24469).mp (by decide +kernel))) hgap
  have hprev := s2L_2713
  have hrat : ((45224373157 : ℚ) / 100000000000) ≤ ((4522437299 : ℚ) / 10000000000) + (24469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224373157 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((4522437299 : ℚ) / 10000000000) : ℚ) : ℝ) + ((24469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24469:ℚ)^(-2:ℤ) : ℝ) = ((24469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2715 : ((((452243733239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24469 < q → q < 24473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24473).mp (by decide +kernel))) hgap
  have hprev := s2L_2714
  have hrat : ((452243733239 : ℚ) / 1000000000000) ≤ ((45224373157 : ℚ) / 100000000000) + (24473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243733239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224373157 : ℚ) / 100000000000) : ℚ) : ℝ) + ((24473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24473:ℚ)^(-2:ℤ) : ℝ) = ((24473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2716 : ((((452243734907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24473 < q → q < 24481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24481).mp (by decide +kernel))) hgap
  have hprev := s2L_2715
  have hrat : ((452243734907 : ℚ) / 1000000000000) ≤ ((452243733239 : ℚ) / 1000000000000) + (24481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243734907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243733239 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24481:ℚ)^(-2:ℤ) : ℝ) = ((24481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2717 : ((((452243736573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24481 < q → q < 24499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24499).mp (by decide +kernel))) hgap
  have hprev := s2L_2716
  have hrat : ((452243736573 : ℚ) / 1000000000000) ≤ ((452243734907 : ℚ) / 1000000000000) + (24499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243736573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243734907 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24499:ℚ)^(-2:ℤ) : ℝ) = ((24499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2718 : ((((452243738237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24499 < q → q < 24509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24509).mp (by decide +kernel))) hgap
  have hprev := s2L_2717
  have hrat : ((452243738237 : ℚ) / 1000000000000) ≤ ((452243736573 : ℚ) / 1000000000000) + (24509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243738237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243736573 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24509:ℚ)^(-2:ℤ) : ℝ) = ((24509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2719 : ((((4522437399 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24509 < q → q < 24517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24517).mp (by decide +kernel))) hgap
  have hprev := s2L_2718
  have hrat : ((4522437399 : ℚ) / 10000000000) ≤ ((452243738237 : ℚ) / 1000000000000) + (24517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522437399 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452243738237 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24517:ℚ)^(-2:ℤ) : ℝ) = ((24517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2720 : ((((226121870781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24517 < q → q < 24527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24527).mp (by decide +kernel))) hgap
  have hprev := s2L_2719
  have hrat : ((226121870781 : ℚ) / 500000000000) ≤ ((4522437399 : ℚ) / 10000000000) + (24527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121870781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522437399 : ℚ) / 10000000000) : ℚ) : ℝ) + ((24527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24527:ℚ)^(-2:ℤ) : ℝ) = ((24527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2721 : ((((452243743223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24533, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24527 < q → q < 24533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24533).mp (by decide +kernel))) hgap
  have hprev := s2L_2720
  have hrat : ((452243743223 : ℚ) / 1000000000000) ≤ ((226121870781 : ℚ) / 500000000000) + (24533:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243743223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121870781 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24533:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24533:ℚ)^(-2:ℤ) : ℝ) = ((24533:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2722 : ((((226121872441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24533 < q → q < 24547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24547).mp (by decide +kernel))) hgap
  have hprev := s2L_2721
  have hrat : ((226121872441 : ℚ) / 500000000000) ≤ ((452243743223 : ℚ) / 1000000000000) + (24547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121872441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243743223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24547:ℚ)^(-2:ℤ) : ℝ) = ((24547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2723 : ((((452243746541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24547 < q → q < 24551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24551).mp (by decide +kernel))) hgap
  have hprev := s2L_2722
  have hrat : ((452243746541 : ℚ) / 1000000000000) ≤ ((226121872441 : ℚ) / 500000000000) + (24551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243746541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121872441 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24551:ℚ)^(-2:ℤ) : ℝ) = ((24551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2724 : ((((452243748197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24551 < q → q < 24571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24571).mp (by decide +kernel))) hgap
  have hprev := s2L_2723
  have hrat : ((452243748197 : ℚ) / 1000000000000) ≤ ((452243746541 : ℚ) / 1000000000000) + (24571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243748197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243746541 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24571:ℚ)^(-2:ℤ) : ℝ) = ((24571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2725 : ((((9044874997 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24571 < q → q < 24593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24593).mp (by decide +kernel))) hgap
  have hprev := s2L_2724
  have hrat : ((9044874997 : ℚ) / 20000000000) ≤ ((452243748197 : ℚ) / 1000000000000) + (24593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044874997 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452243748197 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24593:ℚ)^(-2:ℤ) : ℝ) = ((24593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2726 : ((((904487503 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24593 < q → q < 24611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24611).mp (by decide +kernel))) hgap
  have hprev := s2L_2725
  have hrat : ((904487503 : ℚ) / 2000000000) ≤ ((9044874997 : ℚ) / 20000000000) + (24611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904487503 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((9044874997 : ℚ) / 20000000000) : ℚ) : ℝ) + ((24611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24611:ℚ)^(-2:ℤ) : ℝ) = ((24611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2727 : ((((452243753149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24611 < q → q < 24623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24623).mp (by decide +kernel))) hgap
  have hprev := s2L_2726
  have hrat : ((452243753149 : ℚ) / 1000000000000) ≤ ((904487503 : ℚ) / 2000000000) + (24623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243753149 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((904487503 : ℚ) / 2000000000) : ℚ) : ℝ) + ((24623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24623:ℚ)^(-2:ℤ) : ℝ) = ((24623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2728 : ((((452243754797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24623 < q → q < 24631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24631).mp (by decide +kernel))) hgap
  have hprev := s2L_2727
  have hrat : ((452243754797 : ℚ) / 1000000000000) ≤ ((452243753149 : ℚ) / 1000000000000) + (24631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243754797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243753149 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24631:ℚ)^(-2:ℤ) : ℝ) = ((24631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2729 : ((((452243756441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24631 < q → q < 24659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24659).mp (by decide +kernel))) hgap
  have hprev := s2L_2728
  have hrat : ((452243756441 : ℚ) / 1000000000000) ≤ ((452243754797 : ℚ) / 1000000000000) + (24659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243756441 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243754797 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24659:ℚ)^(-2:ℤ) : ℝ) = ((24659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2730 : ((((452243758083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24659 < q → q < 24671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24671).mp (by decide +kernel))) hgap
  have hprev := s2L_2729
  have hrat : ((452243758083 : ℚ) / 1000000000000) ≤ ((452243756441 : ℚ) / 1000000000000) + (24671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243758083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243756441 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24671:ℚ)^(-2:ℤ) : ℝ) = ((24671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2731 : ((((18089750389 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24671 < q → q < 24677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24677).mp (by decide +kernel))) hgap
  have hprev := s2L_2730
  have hrat : ((18089750389 : ℚ) / 40000000000) ≤ ((452243758083 : ℚ) / 1000000000000) + (24677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089750389 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452243758083 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24677:ℚ)^(-2:ℤ) : ℝ) = ((24677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2732 : ((((226121880683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24677 < q → q < 24683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24683).mp (by decide +kernel))) hgap
  have hprev := s2L_2731
  have hrat : ((226121880683 : ℚ) / 500000000000) ≤ ((18089750389 : ℚ) / 40000000000) + (24683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121880683 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089750389 : ℚ) / 40000000000) : ℚ) : ℝ) + ((24683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24683:ℚ)^(-2:ℤ) : ℝ) = ((24683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2733 : ((((226121881503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24683 < q → q < 24691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24691).mp (by decide +kernel))) hgap
  have hprev := s2L_2732
  have hrat : ((226121881503 : ℚ) / 500000000000) ≤ ((226121880683 : ℚ) / 500000000000) + (24691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121881503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121880683 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24691:ℚ)^(-2:ℤ) : ℝ) = ((24691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2734 : ((((90448752929 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24691 < q → q < 24697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24697).mp (by decide +kernel))) hgap
  have hprev := s2L_2733
  have hrat : ((90448752929 : ℚ) / 200000000000) ≤ ((226121881503 : ℚ) / 500000000000) + (24697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448752929 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121881503 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24697:ℚ)^(-2:ℤ) : ℝ) = ((24697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2735 : ((((226121883141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24697 < q → q < 24709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24709).mp (by decide +kernel))) hgap
  have hprev := s2L_2734
  have hrat : ((226121883141 : ℚ) / 500000000000) ≤ ((90448752929 : ℚ) / 200000000000) + (24709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121883141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448752929 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24709:ℚ)^(-2:ℤ) : ℝ) = ((24709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2736 : ((((113060941979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24709 < q → q < 24733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24733).mp (by decide +kernel))) hgap
  have hprev := s2L_2735
  have hrat : ((113060941979 : ℚ) / 250000000000) ≤ ((226121883141 : ℚ) / 500000000000) + (24733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060941979 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121883141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24733:ℚ)^(-2:ℤ) : ℝ) = ((24733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2737 : ((((113060942387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24733 < q → q < 24749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24749).mp (by decide +kernel))) hgap
  have hprev := s2L_2736
  have hrat : ((113060942387 : ℚ) / 250000000000) ≤ ((113060941979 : ℚ) / 250000000000) + (24749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060942387 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060941979 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24749:ℚ)^(-2:ℤ) : ℝ) = ((24749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2738 : ((((226121885589 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24749 < q → q < 24763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24763).mp (by decide +kernel))) hgap
  have hprev := s2L_2737
  have hrat : ((226121885589 : ℚ) / 500000000000) ≤ ((113060942387 : ℚ) / 250000000000) + (24763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121885589 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060942387 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24763:ℚ)^(-2:ℤ) : ℝ) = ((24763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2739 : ((((56530471601 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24763 < q → q < 24767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24767).mp (by decide +kernel))) hgap
  have hprev := s2L_2738
  have hrat : ((56530471601 : ℚ) / 125000000000) ≤ ((226121885589 : ℚ) / 500000000000) + (24767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530471601 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121885589 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24767:ℚ)^(-2:ℤ) : ℝ) = ((24767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2740 : ((((113060943609 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24767 < q → q < 24781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24781).mp (by decide +kernel))) hgap
  have hprev := s2L_2739
  have hrat : ((113060943609 : ℚ) / 250000000000) ≤ ((56530471601 : ℚ) / 125000000000) + (24781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060943609 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530471601 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24781:ℚ)^(-2:ℤ) : ℝ) = ((24781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2741 : ((((226121888031 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24781 < q → q < 24793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24793).mp (by decide +kernel))) hgap
  have hprev := s2L_2740
  have hrat : ((226121888031 : ℚ) / 500000000000) ≤ ((113060943609 : ℚ) / 250000000000) + (24793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121888031 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060943609 : ℚ) / 250000000000) : ℚ) : ℝ) + ((24793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24793:ℚ)^(-2:ℤ) : ℝ) = ((24793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2742 : ((((56530472211 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24793 < q → q < 24799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24799).mp (by decide +kernel))) hgap
  have hprev := s2L_2741
  have hrat : ((56530472211 : ℚ) / 125000000000) ≤ ((226121888031 : ℚ) / 500000000000) + (24799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530472211 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121888031 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24799:ℚ)^(-2:ℤ) : ℝ) = ((24799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2743 : ((((28265236207 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24799 < q → q < 24809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24809).mp (by decide +kernel))) hgap
  have hprev := s2L_2742
  have hrat : ((28265236207 : ℚ) / 62500000000) ≤ ((56530472211 : ℚ) / 125000000000) + (24809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265236207 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56530472211 : ℚ) / 125000000000) : ℚ) : ℝ) + ((24809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24809:ℚ)^(-2:ℤ) : ℝ) = ((24809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2744 : ((((90448756187 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24809 < q → q < 24821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24821).mp (by decide +kernel))) hgap
  have hprev := s2L_2743
  have hrat : ((90448756187 : ℚ) / 200000000000) ≤ ((28265236207 : ℚ) / 62500000000) + (24821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448756187 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28265236207 : ℚ) / 62500000000) : ℚ) : ℝ) + ((24821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24821:ℚ)^(-2:ℤ) : ℝ) = ((24821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2745 : ((((90448756511 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24821 < q → q < 24841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24841).mp (by decide +kernel))) hgap
  have hprev := s2L_2744
  have hrat : ((90448756511 : ℚ) / 200000000000) ≤ ((90448756187 : ℚ) / 200000000000) + (24841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448756511 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448756187 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24841:ℚ)^(-2:ℤ) : ℝ) = ((24841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2746 : ((((226121892087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24841 < q → q < 24847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24847).mp (by decide +kernel))) hgap
  have hprev := s2L_2745
  have hrat : ((226121892087 : ℚ) / 500000000000) ≤ ((90448756511 : ℚ) / 200000000000) + (24847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121892087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448756511 : ℚ) / 200000000000) : ℚ) : ℝ) + ((24847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24847:ℚ)^(-2:ℤ) : ℝ) = ((24847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2747 : ((((452243785793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24847 < q → q < 24851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24851).mp (by decide +kernel))) hgap
  have hprev := s2L_2746
  have hrat : ((452243785793 : ℚ) / 1000000000000) ≤ ((226121892087 : ℚ) / 500000000000) + (24851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243785793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121892087 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24851:ℚ)^(-2:ℤ) : ℝ) = ((24851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2748 : ((((452243787411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24851 < q → q < 24859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24859).mp (by decide +kernel))) hgap
  have hprev := s2L_2747
  have hrat : ((452243787411 : ℚ) / 1000000000000) ≤ ((452243785793 : ℚ) / 1000000000000) + (24859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243787411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243785793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24859:ℚ)^(-2:ℤ) : ℝ) = ((24859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2749 : ((((226121894513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24859 < q → q < 24877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24877).mp (by decide +kernel))) hgap
  have hprev := s2L_2748
  have hrat : ((226121894513 : ℚ) / 500000000000) ≤ ((452243787411 : ℚ) / 1000000000000) + (24877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121894513 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243787411 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24877:ℚ)^(-2:ℤ) : ℝ) = ((24877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2750 : ((((5653047383 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24877 < q → q < 24889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24889).mp (by decide +kernel))) hgap
  have hprev := s2L_2749
  have hrat : ((5653047383 : ℚ) / 12500000000) ≤ ((226121894513 : ℚ) / 500000000000) + (24889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653047383 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226121894513 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24889:ℚ)^(-2:ℤ) : ℝ) = ((24889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2751 : ((((452243792251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24889 < q → q < 24907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24907).mp (by decide +kernel))) hgap
  have hprev := s2L_2750
  have hrat : ((452243792251 : ℚ) / 1000000000000) ≤ ((5653047383 : ℚ) / 12500000000) + (24907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243792251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653047383 : ℚ) / 12500000000) : ℚ) : ℝ) + ((24907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24907:ℚ)^(-2:ℤ) : ℝ) = ((24907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2752 : ((((452243793861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24907 < q → q < 24917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24917).mp (by decide +kernel))) hgap
  have hprev := s2L_2751
  have hrat : ((452243793861 : ℚ) / 1000000000000) ≤ ((452243792251 : ℚ) / 1000000000000) + (24917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243793861 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243792251 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24917:ℚ)^(-2:ℤ) : ℝ) = ((24917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2753 : ((((452243795471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24917 < q → q < 24919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24919).mp (by decide +kernel))) hgap
  have hprev := s2L_2752
  have hrat : ((452243795471 : ℚ) / 1000000000000) ≤ ((452243793861 : ℚ) / 1000000000000) + (24919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243795471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243793861 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24919:ℚ)^(-2:ℤ) : ℝ) = ((24919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2754 : ((((11306094927 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24919 < q → q < 24923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24923).mp (by decide +kernel))) hgap
  have hprev := s2L_2753
  have hrat : ((11306094927 : ℚ) / 25000000000) ≤ ((452243795471 : ℚ) / 1000000000000) + (24923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306094927 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452243795471 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24923:ℚ)^(-2:ℤ) : ℝ) = ((24923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2755 : ((((452243798687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24923 < q → q < 24943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24943).mp (by decide +kernel))) hgap
  have hprev := s2L_2754
  have hrat : ((452243798687 : ℚ) / 1000000000000) ≤ ((11306094927 : ℚ) / 25000000000) + (24943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243798687 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306094927 : ℚ) / 25000000000) : ℚ) : ℝ) + ((24943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24943:ℚ)^(-2:ℤ) : ℝ) = ((24943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2756 : ((((452243800293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24943 < q → q < 24953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24953).mp (by decide +kernel))) hgap
  have hprev := s2L_2755
  have hrat : ((452243800293 : ℚ) / 1000000000000) ≤ ((452243798687 : ℚ) / 1000000000000) + (24953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243800293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243798687 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24953:ℚ)^(-2:ℤ) : ℝ) = ((24953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2757 : ((((452243801897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24953 < q → q < 24967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24967).mp (by decide +kernel))) hgap
  have hprev := s2L_2756
  have hrat : ((452243801897 : ℚ) / 1000000000000) ≤ ((452243800293 : ℚ) / 1000000000000) + (24967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243801897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243800293 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24967:ℚ)^(-2:ℤ) : ℝ) = ((24967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2758 : ((((904487607 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24967 < q → q < 24971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24971).mp (by decide +kernel))) hgap
  have hprev := s2L_2757
  have hrat : ((904487607 : ℚ) / 2000000000) ≤ ((452243801897 : ℚ) / 1000000000000) + (24971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904487607 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((452243801897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((24971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24971:ℚ)^(-2:ℤ) : ℝ) = ((24971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2759 : ((((226121902551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24971 < q → q < 24977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24977).mp (by decide +kernel))) hgap
  have hprev := s2L_2758
  have hrat : ((226121902551 : ℚ) / 500000000000) ≤ ((904487607 : ℚ) / 2000000000) + (24977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121902551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((904487607 : ℚ) / 2000000000) : ℚ) : ℝ) + ((24977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24977:ℚ)^(-2:ℤ) : ℝ) = ((24977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2760 : ((((28265237919 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24977 < q → q < 24979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24979).mp (by decide +kernel))) hgap
  have hprev := s2L_2759
  have hrat : ((28265237919 : ℚ) / 62500000000) ≤ ((226121902551 : ℚ) / 500000000000) + (24979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265237919 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121902551 : ℚ) / 500000000000) : ℚ) : ℝ) + ((24979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24979:ℚ)^(-2:ℤ) : ℝ) = ((24979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2761 : ((((90448761661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 24989, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24979 < q → q < 24989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 24989).mp (by decide +kernel))) hgap
  have hprev := s2L_2760
  have hrat : ((90448761661 : ℚ) / 200000000000) ≤ ((28265237919 : ℚ) / 62500000000) + (24989:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448761661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28265237919 : ℚ) / 62500000000) : ℚ) : ℝ) + ((24989:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((24989:ℚ)^(-2:ℤ) : ℝ) = ((24989:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2762 : ((((452243809903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 24989 < q → q < 25013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25013).mp (by decide +kernel))) hgap
  have hprev := s2L_2761
  have hrat : ((452243809903 : ℚ) / 1000000000000) ≤ ((90448761661 : ℚ) / 200000000000) + (25013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243809903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448761661 : ℚ) / 200000000000) : ℚ) : ℝ) + ((25013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25013:ℚ)^(-2:ℤ) : ℝ) = ((25013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2763 : ((((452243811499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25013 < q → q < 25031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25031).mp (by decide +kernel))) hgap
  have hprev := s2L_2762
  have hrat : ((452243811499 : ℚ) / 1000000000000) ≤ ((452243809903 : ℚ) / 1000000000000) + (25031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243811499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243809903 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25031:ℚ)^(-2:ℤ) : ℝ) = ((25031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2764 : ((((226121906547 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25031 < q → q < 25033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25033).mp (by decide +kernel))) hgap
  have hprev := s2L_2763
  have hrat : ((226121906547 : ℚ) / 500000000000) ≤ ((452243811499 : ℚ) / 1000000000000) + (25033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121906547 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243811499 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25033:ℚ)^(-2:ℤ) : ℝ) = ((25033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2765 : ((((452243814689 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25033 < q → q < 25037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25037).mp (by decide +kernel))) hgap
  have hprev := s2L_2764
  have hrat : ((452243814689 : ℚ) / 1000000000000) ≤ ((226121906547 : ℚ) / 500000000000) + (25037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243814689 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121906547 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25037:ℚ)^(-2:ℤ) : ℝ) = ((25037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2766 : ((((452243816281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25037 < q → q < 25057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25057).mp (by decide +kernel))) hgap
  have hprev := s2L_2765
  have hrat : ((452243816281 : ℚ) / 1000000000000) ≤ ((452243814689 : ℚ) / 1000000000000) + (25057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243816281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243814689 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25057:ℚ)^(-2:ℤ) : ℝ) = ((25057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2767 : ((((452243817871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25057 < q → q < 25073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25073).mp (by decide +kernel))) hgap
  have hprev := s2L_2766
  have hrat : ((452243817871 : ℚ) / 1000000000000) ≤ ((452243816281 : ℚ) / 1000000000000) + (25073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243817871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243816281 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25073:ℚ)^(-2:ℤ) : ℝ) = ((25073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2768 : ((((452243819459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25073 < q → q < 25087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25087).mp (by decide +kernel))) hgap
  have hprev := s2L_2767
  have hrat : ((452243819459 : ℚ) / 1000000000000) ≤ ((452243817871 : ℚ) / 1000000000000) + (25087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243819459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243817871 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25087:ℚ)^(-2:ℤ) : ℝ) = ((25087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2769 : ((((226121910523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25087 < q → q < 25097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25097).mp (by decide +kernel))) hgap
  have hprev := s2L_2768
  have hrat : ((226121910523 : ℚ) / 500000000000) ≤ ((452243819459 : ℚ) / 1000000000000) + (25097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121910523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243819459 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25097:ℚ)^(-2:ℤ) : ℝ) = ((25097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2770 : ((((452243822631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25097 < q → q < 25111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25111).mp (by decide +kernel))) hgap
  have hprev := s2L_2769
  have hrat : ((452243822631 : ℚ) / 1000000000000) ≤ ((226121910523 : ℚ) / 500000000000) + (25111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243822631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121910523 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25111:ℚ)^(-2:ℤ) : ℝ) = ((25111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2771 : ((((56530478027 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25111 < q → q < 25117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25117).mp (by decide +kernel))) hgap
  have hprev := s2L_2770
  have hrat : ((56530478027 : ℚ) / 125000000000) ≤ ((452243822631 : ℚ) / 1000000000000) + (25117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530478027 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243822631 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25117:ℚ)^(-2:ℤ) : ℝ) = ((25117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2772 : ((((2261219129 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25117 < q → q < 25121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25121).mp (by decide +kernel))) hgap
  have hprev := s2L_2771
  have hrat : ((2261219129 : ℚ) / 5000000000) ≤ ((56530478027 : ℚ) / 125000000000) + (25121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261219129 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((56530478027 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25121:ℚ)^(-2:ℤ) : ℝ) = ((25121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2773 : ((((452243827383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25121 < q → q < 25127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25127).mp (by decide +kernel))) hgap
  have hprev := s2L_2772
  have hrat : ((452243827383 : ℚ) / 1000000000000) ≤ ((2261219129 : ℚ) / 5000000000) + (25127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243827383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2261219129 : ℚ) / 5000000000) : ℚ) : ℝ) + ((25127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25127:ℚ)^(-2:ℤ) : ℝ) = ((25127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2774 : ((((113060957241 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25127 < q → q < 25147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25147).mp (by decide +kernel))) hgap
  have hprev := s2L_2773
  have hrat : ((113060957241 : ℚ) / 250000000000) ≤ ((452243827383 : ℚ) / 1000000000000) + (25147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060957241 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243827383 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25147:ℚ)^(-2:ℤ) : ℝ) = ((25147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2775 : ((((28265239409 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25147 < q → q < 25153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25153).mp (by decide +kernel))) hgap
  have hprev := s2L_2774
  have hrat : ((28265239409 : ℚ) / 62500000000) ≤ ((113060957241 : ℚ) / 250000000000) + (25153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265239409 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113060957241 : ℚ) / 250000000000) : ℚ) : ℝ) + ((25153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25153:ℚ)^(-2:ℤ) : ℝ) = ((25153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2776 : ((((452243832123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25153 < q → q < 25163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25163).mp (by decide +kernel))) hgap
  have hprev := s2L_2775
  have hrat : ((452243832123 : ℚ) / 1000000000000) ≤ ((28265239409 : ℚ) / 62500000000) + (25163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243832123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265239409 : ℚ) / 62500000000) : ℚ) : ℝ) + ((25163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25163:ℚ)^(-2:ℤ) : ℝ) = ((25163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2777 : ((((452243833701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25163 < q → q < 25169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25169).mp (by decide +kernel))) hgap
  have hprev := s2L_2776
  have hrat : ((452243833701 : ℚ) / 1000000000000) ≤ ((452243832123 : ℚ) / 1000000000000) + (25169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243833701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243832123 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25169:ℚ)^(-2:ℤ) : ℝ) = ((25169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2778 : ((((452243835279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25169 < q → q < 25171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25171).mp (by decide +kernel))) hgap
  have hprev := s2L_2777
  have hrat : ((452243835279 : ℚ) / 1000000000000) ≤ ((452243833701 : ℚ) / 1000000000000) + (25171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243835279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243833701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25171:ℚ)^(-2:ℤ) : ℝ) = ((25171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2779 : ((((90448767371 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25171 < q → q < 25183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25183).mp (by decide +kernel))) hgap
  have hprev := s2L_2778
  have hrat : ((90448767371 : ℚ) / 200000000000) ≤ ((452243835279 : ℚ) / 1000000000000) + (25183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448767371 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243835279 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25183:ℚ)^(-2:ℤ) : ℝ) = ((25183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2780 : ((((452243838431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25183 < q → q < 25189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25189).mp (by decide +kernel))) hgap
  have hprev := s2L_2779
  have hrat : ((452243838431 : ℚ) / 1000000000000) ≤ ((90448767371 : ℚ) / 200000000000) + (25189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243838431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448767371 : ℚ) / 200000000000) : ℚ) : ℝ) + ((25189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25189:ℚ)^(-2:ℤ) : ℝ) = ((25189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2781 : ((((452243840003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25189 < q → q < 25219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25219).mp (by decide +kernel))) hgap
  have hprev := s2L_2780
  have hrat : ((452243840003 : ℚ) / 1000000000000) ≤ ((452243838431 : ℚ) / 1000000000000) + (25219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243840003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243838431 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25219:ℚ)^(-2:ℤ) : ℝ) = ((25219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2782 : ((((226121920787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25219 < q → q < 25229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25229).mp (by decide +kernel))) hgap
  have hprev := s2L_2781
  have hrat : ((226121920787 : ℚ) / 500000000000) ≤ ((452243840003 : ℚ) / 1000000000000) + (25229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121920787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243840003 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25229:ℚ)^(-2:ℤ) : ℝ) = ((25229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2783 : ((((56530480393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25229 < q → q < 25237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25237).mp (by decide +kernel))) hgap
  have hprev := s2L_2782
  have hrat : ((56530480393 : ℚ) / 125000000000) ≤ ((226121920787 : ℚ) / 500000000000) + (25237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530480393 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121920787 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25237:ℚ)^(-2:ℤ) : ℝ) = ((25237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2784 : ((((452243844713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25237 < q → q < 25243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25243).mp (by decide +kernel))) hgap
  have hprev := s2L_2783
  have hrat : ((452243844713 : ℚ) / 1000000000000) ≤ ((56530480393 : ℚ) / 125000000000) + (25243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243844713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530480393 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25243:ℚ)^(-2:ℤ) : ℝ) = ((25243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2785 : ((((452243846281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25243 < q → q < 25247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25247).mp (by decide +kernel))) hgap
  have hprev := s2L_2784
  have hrat : ((452243846281 : ℚ) / 1000000000000) ≤ ((452243844713 : ℚ) / 1000000000000) + (25247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243846281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243844713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25247:ℚ)^(-2:ℤ) : ℝ) = ((25247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2786 : ((((452243847849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25247 < q → q < 25253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25253).mp (by decide +kernel))) hgap
  have hprev := s2L_2785
  have hrat : ((452243847849 : ℚ) / 1000000000000) ≤ ((452243846281 : ℚ) / 1000000000000) + (25253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243847849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243846281 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25253:ℚ)^(-2:ℤ) : ℝ) = ((25253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2787 : ((((56530481177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25253 < q → q < 25261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25261).mp (by decide +kernel))) hgap
  have hprev := s2L_2786
  have hrat : ((56530481177 : ℚ) / 125000000000) ≤ ((452243847849 : ℚ) / 1000000000000) + (25261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530481177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243847849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25261:ℚ)^(-2:ℤ) : ℝ) = ((25261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2788 : ((((226121925489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25261 < q → q < 25301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25301).mp (by decide +kernel))) hgap
  have hprev := s2L_2787
  have hrat : ((226121925489 : ℚ) / 500000000000) ≤ ((56530481177 : ℚ) / 125000000000) + (25301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121925489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530481177 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25301:ℚ)^(-2:ℤ) : ℝ) = ((25301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2789 : ((((452243852539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25301 < q → q < 25303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25303).mp (by decide +kernel))) hgap
  have hprev := s2L_2788
  have hrat : ((452243852539 : ℚ) / 1000000000000) ≤ ((226121925489 : ℚ) / 500000000000) + (25303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243852539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121925489 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25303:ℚ)^(-2:ℤ) : ℝ) = ((25303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2790 : ((((4522438541 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25303 < q → q < 25307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25307).mp (by decide +kernel))) hgap
  have hprev := s2L_2789
  have hrat : ((4522438541 : ℚ) / 10000000000) ≤ ((452243852539 : ℚ) / 1000000000000) + (25307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522438541 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452243852539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25307:ℚ)^(-2:ℤ) : ℝ) = ((25307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2791 : ((((452243855661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25307 < q → q < 25309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25309).mp (by decide +kernel))) hgap
  have hprev := s2L_2790
  have hrat : ((452243855661 : ℚ) / 1000000000000) ≤ ((4522438541 : ℚ) / 10000000000) + (25309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243855661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522438541 : ℚ) / 10000000000) : ℚ) : ℝ) + ((25309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25309:ℚ)^(-2:ℤ) : ℝ) = ((25309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2792 : ((((22612192861 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25309 < q → q < 25321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25321).mp (by decide +kernel))) hgap
  have hprev := s2L_2791
  have hrat : ((22612192861 : ℚ) / 50000000000) ≤ ((452243855661 : ℚ) / 1000000000000) + (25321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612192861 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243855661 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25321:ℚ)^(-2:ℤ) : ℝ) = ((25321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2793 : ((((452243858777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25321 < q → q < 25339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25339).mp (by decide +kernel))) hgap
  have hprev := s2L_2792
  have hrat : ((452243858777 : ℚ) / 1000000000000) ≤ ((22612192861 : ℚ) / 50000000000) + (25339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243858777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612192861 : ℚ) / 50000000000) : ℚ) : ℝ) + ((25339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25339:ℚ)^(-2:ℤ) : ℝ) = ((25339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2794 : ((((452243860333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25339 < q → q < 25343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25343).mp (by decide +kernel))) hgap
  have hprev := s2L_2793
  have hrat : ((452243860333 : ℚ) / 1000000000000) ≤ ((452243858777 : ℚ) / 1000000000000) + (25343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243860333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243858777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25343:ℚ)^(-2:ℤ) : ℝ) = ((25343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2795 : ((((452243861889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25343 < q → q < 25349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25349).mp (by decide +kernel))) hgap
  have hprev := s2L_2794
  have hrat : ((452243861889 : ℚ) / 1000000000000) ≤ ((452243860333 : ℚ) / 1000000000000) + (25349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243861889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243860333 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25349:ℚ)^(-2:ℤ) : ℝ) = ((25349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2796 : ((((113060965861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25349 < q → q < 25357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25357).mp (by decide +kernel))) hgap
  have hprev := s2L_2795
  have hrat : ((113060965861 : ℚ) / 250000000000) ≤ ((452243861889 : ℚ) / 1000000000000) + (25357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060965861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243861889 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25357:ℚ)^(-2:ℤ) : ℝ) = ((25357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2797 : ((((226121932499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25357 < q → q < 25367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25367).mp (by decide +kernel))) hgap
  have hprev := s2L_2796
  have hrat : ((226121932499 : ℚ) / 500000000000) ≤ ((113060965861 : ℚ) / 250000000000) + (25367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121932499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060965861 : ℚ) / 250000000000) : ℚ) : ℝ) + ((25367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25367:ℚ)^(-2:ℤ) : ℝ) = ((25367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2798 : ((((452243866551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25367 < q → q < 25373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25373).mp (by decide +kernel))) hgap
  have hprev := s2L_2797
  have hrat : ((452243866551 : ℚ) / 1000000000000) ≤ ((226121932499 : ℚ) / 500000000000) + (25373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243866551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121932499 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25373:ℚ)^(-2:ℤ) : ℝ) = ((25373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2799 : ((((226121934051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25373 < q → q < 25391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25391).mp (by decide +kernel))) hgap
  have hprev := s2L_2798
  have hrat : ((226121934051 : ℚ) / 500000000000) ≤ ((452243866551 : ℚ) / 1000000000000) + (25391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121934051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243866551 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25391:ℚ)^(-2:ℤ) : ℝ) = ((25391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2800 : ((((9044877393 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25391 < q → q < 25409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25409).mp (by decide +kernel))) hgap
  have hprev := s2L_2799
  have hrat : ((9044877393 : ℚ) / 20000000000) ≤ ((226121934051 : ℚ) / 500000000000) + (25409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044877393 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226121934051 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25409:ℚ)^(-2:ℤ) : ℝ) = ((25409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2801 : ((((226121935599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25409 < q → q < 25411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25411).mp (by decide +kernel))) hgap
  have hprev := s2L_2800
  have hrat : ((226121935599 : ℚ) / 500000000000) ≤ ((9044877393 : ℚ) / 20000000000) + (25411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121935599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9044877393 : ℚ) / 20000000000) : ℚ) : ℝ) + ((25411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25411:ℚ)^(-2:ℤ) : ℝ) = ((25411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2802 : ((((90448774549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25411 < q → q < 25423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25423).mp (by decide +kernel))) hgap
  have hprev := s2L_2801
  have hrat : ((90448774549 : ℚ) / 200000000000) ≤ ((226121935599 : ℚ) / 500000000000) + (25423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448774549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121935599 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25423:ℚ)^(-2:ℤ) : ℝ) = ((25423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2803 : ((((45224387429 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25423 < q → q < 25439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25439).mp (by decide +kernel))) hgap
  have hprev := s2L_2802
  have hrat : ((45224387429 : ℚ) / 100000000000) ≤ ((90448774549 : ℚ) / 200000000000) + (25439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224387429 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90448774549 : ℚ) / 200000000000) : ℚ) : ℝ) + ((25439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25439:ℚ)^(-2:ℤ) : ℝ) = ((25439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2804 : ((((226121937917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25439 < q → q < 25447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25447).mp (by decide +kernel))) hgap
  have hprev := s2L_2803
  have hrat : ((226121937917 : ℚ) / 500000000000) ≤ ((45224387429 : ℚ) / 100000000000) + (25447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121937917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224387429 : ℚ) / 100000000000) : ℚ) : ℝ) + ((25447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25447:ℚ)^(-2:ℤ) : ℝ) = ((25447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2805 : ((((452243877377 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25447 < q → q < 25453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25453).mp (by decide +kernel))) hgap
  have hprev := s2L_2804
  have hrat : ((452243877377 : ℚ) / 1000000000000) ≤ ((226121937917 : ℚ) / 500000000000) + (25453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243877377 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121937917 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25453:ℚ)^(-2:ℤ) : ℝ) = ((25453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2806 : ((((11306096973 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25453 < q → q < 25457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25457).mp (by decide +kernel))) hgap
  have hprev := s2L_2805
  have hrat : ((11306096973 : ℚ) / 25000000000) ≤ ((452243877377 : ℚ) / 1000000000000) + (25457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306096973 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452243877377 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25457:ℚ)^(-2:ℤ) : ℝ) = ((25457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2807 : ((((226121940231 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25457 < q → q < 25463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25463).mp (by decide +kernel))) hgap
  have hprev := s2L_2806
  have hrat : ((226121940231 : ℚ) / 500000000000) ≤ ((11306096973 : ℚ) / 25000000000) + (25463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121940231 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11306096973 : ℚ) / 25000000000) : ℚ) : ℝ) + ((25463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25463:ℚ)^(-2:ℤ) : ℝ) = ((25463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2808 : ((((452243882003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25463 < q → q < 25469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25469).mp (by decide +kernel))) hgap
  have hprev := s2L_2807
  have hrat : ((452243882003 : ℚ) / 1000000000000) ≤ ((226121940231 : ℚ) / 500000000000) + (25469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243882003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121940231 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25469:ℚ)^(-2:ℤ) : ℝ) = ((25469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2809 : ((((56530485443 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25469 < q → q < 25471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25471).mp (by decide +kernel))) hgap
  have hprev := s2L_2808
  have hrat : ((56530485443 : ℚ) / 125000000000) ≤ ((452243882003 : ℚ) / 1000000000000) + (25471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530485443 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243882003 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25471:ℚ)^(-2:ℤ) : ℝ) = ((25471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2810 : ((((452243885079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25471 < q → q < 25523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25523).mp (by decide +kernel))) hgap
  have hprev := s2L_2809
  have hrat : ((452243885079 : ℚ) / 1000000000000) ≤ ((56530485443 : ℚ) / 125000000000) + (25523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243885079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530485443 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25523:ℚ)^(-2:ℤ) : ℝ) = ((25523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2811 : ((((113060971653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25523 < q → q < 25537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25537).mp (by decide +kernel))) hgap
  have hprev := s2L_2810
  have hrat : ((113060971653 : ℚ) / 250000000000) ≤ ((452243885079 : ℚ) / 1000000000000) + (25537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060971653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243885079 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25537:ℚ)^(-2:ℤ) : ℝ) = ((25537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2812 : ((((28265243009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25537 < q → q < 25541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25541).mp (by decide +kernel))) hgap
  have hprev := s2L_2811
  have hrat : ((28265243009 : ℚ) / 62500000000) ≤ ((113060971653 : ℚ) / 250000000000) + (25541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265243009 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113060971653 : ℚ) / 250000000000) : ℚ) : ℝ) + ((25541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25541:ℚ)^(-2:ℤ) : ℝ) = ((25541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2813 : ((((226121944837 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25541 < q → q < 25561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25561).mp (by decide +kernel))) hgap
  have hprev := s2L_2812
  have hrat : ((226121944837 : ℚ) / 500000000000) ≤ ((28265243009 : ℚ) / 62500000000) + (25561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121944837 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265243009 : ℚ) / 62500000000) : ℚ) : ℝ) + ((25561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25561:ℚ)^(-2:ℤ) : ℝ) = ((25561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2814 : ((((226121945601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25561 < q → q < 25577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25577).mp (by decide +kernel))) hgap
  have hprev := s2L_2813
  have hrat : ((226121945601 : ℚ) / 500000000000) ≤ ((226121944837 : ℚ) / 500000000000) + (25577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121945601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121944837 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25577:ℚ)^(-2:ℤ) : ℝ) = ((25577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2815 : ((((45224389273 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25577 < q → q < 25579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25579).mp (by decide +kernel))) hgap
  have hprev := s2L_2814
  have hrat : ((45224389273 : ℚ) / 100000000000) ≤ ((226121945601 : ℚ) / 500000000000) + (25579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224389273 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121945601 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25579:ℚ)^(-2:ℤ) : ℝ) = ((25579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2816 : ((((452243894257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25579 < q → q < 25583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25583).mp (by decide +kernel))) hgap
  have hprev := s2L_2815
  have hrat : ((452243894257 : ℚ) / 1000000000000) ≤ ((45224389273 : ℚ) / 100000000000) + (25583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243894257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224389273 : ℚ) / 100000000000) : ℚ) : ℝ) + ((25583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25583:ℚ)^(-2:ℤ) : ℝ) = ((25583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2817 : ((((56530486973 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25589, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25583 < q → q < 25589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25589).mp (by decide +kernel))) hgap
  have hprev := s2L_2816
  have hrat : ((56530486973 : ℚ) / 125000000000) ≤ ((452243894257 : ℚ) / 1000000000000) + (25589:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530486973 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243894257 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25589:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25589:ℚ)^(-2:ℤ) : ℝ) = ((25589:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2818 : ((((452243897309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25589 < q → q < 25601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25601).mp (by decide +kernel))) hgap
  have hprev := s2L_2817
  have hrat : ((452243897309 : ℚ) / 1000000000000) ≤ ((56530486973 : ℚ) / 125000000000) + (25601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243897309 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530486973 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25601:ℚ)^(-2:ℤ) : ℝ) = ((25601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2819 : ((((226121949417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25601 < q → q < 25603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25603).mp (by decide +kernel))) hgap
  have hprev := s2L_2818
  have hrat : ((226121949417 : ℚ) / 500000000000) ≤ ((452243897309 : ℚ) / 1000000000000) + (25603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121949417 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243897309 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25603:ℚ)^(-2:ℤ) : ℝ) = ((25603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2820 : ((((226121950179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25603 < q → q < 25609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25609).mp (by decide +kernel))) hgap
  have hprev := s2L_2819
  have hrat : ((226121950179 : ℚ) / 500000000000) ≤ ((226121949417 : ℚ) / 500000000000) + (25609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121950179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121949417 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25609:ℚ)^(-2:ℤ) : ℝ) = ((25609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2821 : ((((452243901881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25609 < q → q < 25621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25621).mp (by decide +kernel))) hgap
  have hprev := s2L_2820
  have hrat : ((452243901881 : ℚ) / 1000000000000) ≤ ((226121950179 : ℚ) / 500000000000) + (25621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243901881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121950179 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25621:ℚ)^(-2:ℤ) : ℝ) = ((25621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2822 : ((((226121951701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25621 < q → q < 25633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25633).mp (by decide +kernel))) hgap
  have hprev := s2L_2821
  have hrat : ((226121951701 : ℚ) / 500000000000) ≤ ((452243901881 : ℚ) / 1000000000000) + (25633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121951701 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243901881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25633:ℚ)^(-2:ℤ) : ℝ) = ((25633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2823 : ((((452243904923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25633 < q → q < 25639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25639).mp (by decide +kernel))) hgap
  have hprev := s2L_2822
  have hrat : ((452243904923 : ℚ) / 1000000000000) ≤ ((226121951701 : ℚ) / 500000000000) + (25639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243904923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121951701 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25639:ℚ)^(-2:ℤ) : ℝ) = ((25639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2824 : ((((452243906443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25639 < q → q < 25643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25643).mp (by decide +kernel))) hgap
  have hprev := s2L_2823
  have hrat : ((452243906443 : ℚ) / 1000000000000) ≤ ((452243904923 : ℚ) / 1000000000000) + (25643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243906443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243904923 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25643:ℚ)^(-2:ℤ) : ℝ) = ((25643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2825 : ((((226121953981 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25643 < q → q < 25657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25657).mp (by decide +kernel))) hgap
  have hprev := s2L_2824
  have hrat : ((226121953981 : ℚ) / 500000000000) ≤ ((452243906443 : ℚ) / 1000000000000) + (25657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121953981 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243906443 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25657:ℚ)^(-2:ℤ) : ℝ) = ((25657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2826 : ((((452243909479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25667, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25657 < q → q < 25667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25667).mp (by decide +kernel))) hgap
  have hprev := s2L_2825
  have hrat : ((452243909479 : ℚ) / 1000000000000) ≤ ((226121953981 : ℚ) / 500000000000) + (25667:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243909479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121953981 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25667:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25667:ℚ)^(-2:ℤ) : ℝ) = ((25667:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2827 : ((((113060977749 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25667 < q → q < 25673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25673).mp (by decide +kernel))) hgap
  have hprev := s2L_2826
  have hrat : ((113060977749 : ℚ) / 250000000000) ≤ ((452243909479 : ℚ) / 1000000000000) + (25673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060977749 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243909479 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25673:ℚ)^(-2:ℤ) : ℝ) = ((25673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2828 : ((((7066311133 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25673 < q → q < 25679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25679).mp (by decide +kernel))) hgap
  have hprev := s2L_2827
  have hrat : ((7066311133 : ℚ) / 15625000000) ≤ ((113060977749 : ℚ) / 250000000000) + (25679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066311133 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((113060977749 : ℚ) / 250000000000) : ℚ) : ℝ) + ((25679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25679:ℚ)^(-2:ℤ) : ℝ) = ((25679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2829 : ((((226121957013 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25679 < q → q < 25693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25693).mp (by decide +kernel))) hgap
  have hprev := s2L_2828
  have hrat : ((226121957013 : ℚ) / 500000000000) ≤ ((7066311133 : ℚ) / 15625000000) + (25693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121957013 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7066311133 : ℚ) / 15625000000) : ℚ) : ℝ) + ((25693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25693:ℚ)^(-2:ℤ) : ℝ) = ((25693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2830 : ((((452243915539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25693 < q → q < 25703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25703).mp (by decide +kernel))) hgap
  have hprev := s2L_2829
  have hrat : ((452243915539 : ℚ) / 1000000000000) ≤ ((226121957013 : ℚ) / 500000000000) + (25703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243915539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121957013 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25703:ℚ)^(-2:ℤ) : ℝ) = ((25703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2831 : ((((452243917051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25703 < q → q < 25717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25717).mp (by decide +kernel))) hgap
  have hprev := s2L_2830
  have hrat : ((452243917051 : ℚ) / 1000000000000) ≤ ((452243915539 : ℚ) / 1000000000000) + (25717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243917051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243915539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25717:ℚ)^(-2:ℤ) : ℝ) = ((25717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2832 : ((((452243918561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25717 < q → q < 25733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25733).mp (by decide +kernel))) hgap
  have hprev := s2L_2831
  have hrat : ((452243918561 : ℚ) / 1000000000000) ≤ ((452243917051 : ℚ) / 1000000000000) + (25733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243918561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243917051 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25733:ℚ)^(-2:ℤ) : ℝ) = ((25733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2833 : ((((45224392007 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25733 < q → q < 25741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25741).mp (by decide +kernel))) hgap
  have hprev := s2L_2832
  have hrat : ((45224392007 : ℚ) / 100000000000) ≤ ((452243918561 : ℚ) / 1000000000000) + (25741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224392007 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452243918561 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25741:ℚ)^(-2:ℤ) : ℝ) = ((25741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2834 : ((((226121960789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25741 < q → q < 25747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25747).mp (by decide +kernel))) hgap
  have hprev := s2L_2833
  have hrat : ((226121960789 : ℚ) / 500000000000) ≤ ((45224392007 : ℚ) / 100000000000) + (25747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121960789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224392007 : ℚ) / 100000000000) : ℚ) : ℝ) + ((25747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25747:ℚ)^(-2:ℤ) : ℝ) = ((25747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2835 : ((((90448784617 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25747 < q → q < 25759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25759).mp (by decide +kernel))) hgap
  have hprev := s2L_2834
  have hrat : ((90448784617 : ℚ) / 200000000000) ≤ ((226121960789 : ℚ) / 500000000000) + (25759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448784617 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121960789 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25759:ℚ)^(-2:ℤ) : ℝ) = ((25759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2836 : ((((452243924591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25759 < q → q < 25763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25763).mp (by decide +kernel))) hgap
  have hprev := s2L_2835
  have hrat : ((452243924591 : ℚ) / 1000000000000) ≤ ((90448784617 : ℚ) / 200000000000) + (25763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243924591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448784617 : ℚ) / 200000000000) : ℚ) : ℝ) + ((25763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25763:ℚ)^(-2:ℤ) : ℝ) = ((25763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2837 : ((((28265245381 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25771, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25763 < q → q < 25771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25771).mp (by decide +kernel))) hgap
  have hprev := s2L_2836
  have hrat : ((28265245381 : ℚ) / 62500000000) ≤ ((452243924591 : ℚ) / 1000000000000) + (25771:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265245381 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452243924591 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25771:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25771:ℚ)^(-2:ℤ) : ℝ) = ((25771:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2838 : ((((452243927599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25771 < q → q < 25793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25793).mp (by decide +kernel))) hgap
  have hprev := s2L_2837
  have hrat : ((452243927599 : ℚ) / 1000000000000) ≤ ((28265245381 : ℚ) / 62500000000) + (25793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243927599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265245381 : ℚ) / 62500000000) : ℚ) : ℝ) + ((25793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25793:ℚ)^(-2:ℤ) : ℝ) = ((25793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2839 : ((((452243929101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25793 < q → q < 25799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25799).mp (by decide +kernel))) hgap
  have hprev := s2L_2838
  have hrat : ((452243929101 : ℚ) / 1000000000000) ≤ ((452243927599 : ℚ) / 1000000000000) + (25799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243929101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243927599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25799:ℚ)^(-2:ℤ) : ℝ) = ((25799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2840 : ((((452243930603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25799 < q → q < 25801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25801).mp (by decide +kernel))) hgap
  have hprev := s2L_2839
  have hrat : ((452243930603 : ℚ) / 1000000000000) ≤ ((452243929101 : ℚ) / 1000000000000) + (25801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243930603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243929101 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25801:ℚ)^(-2:ℤ) : ℝ) = ((25801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2841 : ((((452243932103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25801 < q → q < 25819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25819).mp (by decide +kernel))) hgap
  have hprev := s2L_2840
  have hrat : ((452243932103 : ℚ) / 1000000000000) ≤ ((452243930603 : ℚ) / 1000000000000) + (25819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243932103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243930603 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25819:ℚ)^(-2:ℤ) : ℝ) = ((25819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2842 : ((((565304917 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25819 < q → q < 25841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25841).mp (by decide +kernel))) hgap
  have hprev := s2L_2841
  have hrat : ((565304917 : ℚ) / 1250000000) ≤ ((452243932103 : ℚ) / 1000000000000) + (25841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((565304917 : ℚ) / 1250000000) : ℚ) : ℝ) ≤ ((((452243932103 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25841:ℚ)^(-2:ℤ) : ℝ) = ((25841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2843 : ((((56530491887 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25841 < q → q < 25847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25847).mp (by decide +kernel))) hgap
  have hprev := s2L_2842
  have hrat : ((56530491887 : ℚ) / 125000000000) ≤ ((565304917 : ℚ) / 1250000000) + (25847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530491887 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((565304917 : ℚ) / 1250000000) : ℚ) : ℝ) + ((25847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25847:ℚ)^(-2:ℤ) : ℝ) = ((25847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2844 : ((((28265246037 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25849, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25847 < q → q < 25849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25849).mp (by decide +kernel))) hgap
  have hprev := s2L_2843
  have hrat : ((28265246037 : ℚ) / 62500000000) ≤ ((56530491887 : ℚ) / 125000000000) + (25849:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265246037 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56530491887 : ℚ) / 125000000000) : ℚ) : ℝ) + ((25849:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25849:ℚ)^(-2:ℤ) : ℝ) = ((25849:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2845 : ((((226121969043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25849 < q → q < 25867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25867).mp (by decide +kernel))) hgap
  have hprev := s2L_2844
  have hrat : ((226121969043 : ℚ) / 500000000000) ≤ ((28265246037 : ℚ) / 62500000000) + (25867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121969043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265246037 : ℚ) / 62500000000) : ℚ) : ℝ) + ((25867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25867:ℚ)^(-2:ℤ) : ℝ) = ((25867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2846 : ((((452243939579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25867 < q → q < 25873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25873).mp (by decide +kernel))) hgap
  have hprev := s2L_2845
  have hrat : ((452243939579 : ℚ) / 1000000000000) ≤ ((226121969043 : ℚ) / 500000000000) + (25873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243939579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121969043 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25873:ℚ)^(-2:ℤ) : ℝ) = ((25873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2847 : ((((452243941071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25873 < q → q < 25889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25889).mp (by decide +kernel))) hgap
  have hprev := s2L_2846
  have hrat : ((452243941071 : ℚ) / 1000000000000) ≤ ((452243939579 : ℚ) / 1000000000000) + (25889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243941071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243939579 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25889:ℚ)^(-2:ℤ) : ℝ) = ((25889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2848 : ((((452243942561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25889 < q → q < 25903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25903).mp (by decide +kernel))) hgap
  have hprev := s2L_2847
  have hrat : ((452243942561 : ℚ) / 1000000000000) ≤ ((452243941071 : ℚ) / 1000000000000) + (25903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243942561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243941071 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25903:ℚ)^(-2:ℤ) : ℝ) = ((25903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2849 : ((((9044878881 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25903 < q → q < 25913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25913).mp (by decide +kernel))) hgap
  have hprev := s2L_2848
  have hrat : ((9044878881 : ℚ) / 20000000000) ≤ ((452243942561 : ℚ) / 1000000000000) + (25913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044878881 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452243942561 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25913:ℚ)^(-2:ℤ) : ℝ) = ((25913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2850 : ((((226121972769 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25913 < q → q < 25919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25919).mp (by decide +kernel))) hgap
  have hprev := s2L_2849
  have hrat : ((226121972769 : ℚ) / 500000000000) ≤ ((9044878881 : ℚ) / 20000000000) + (25919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121972769 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9044878881 : ℚ) / 20000000000) : ℚ) : ℝ) + ((25919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25919:ℚ)^(-2:ℤ) : ℝ) = ((25919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2851 : ((((18089757881 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25919 < q → q < 25931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25931).mp (by decide +kernel))) hgap
  have hprev := s2L_2850
  have hrat : ((18089757881 : ℚ) / 40000000000) ≤ ((226121972769 : ℚ) / 500000000000) + (25931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089757881 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226121972769 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25931:ℚ)^(-2:ℤ) : ℝ) = ((25931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2852 : ((((452243948511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25931 < q → q < 25933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25933).mp (by decide +kernel))) hgap
  have hprev := s2L_2851
  have hrat : ((452243948511 : ℚ) / 1000000000000) ≤ ((18089757881 : ℚ) / 40000000000) + (25933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243948511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089757881 : ℚ) / 40000000000) : ℚ) : ℝ) + ((25933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25933:ℚ)^(-2:ℤ) : ℝ) = ((25933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2853 : ((((452243949997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25933 < q → q < 25939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25939).mp (by decide +kernel))) hgap
  have hprev := s2L_2852
  have hrat : ((452243949997 : ℚ) / 1000000000000) ≤ ((452243948511 : ℚ) / 1000000000000) + (25939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243949997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243948511 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25939:ℚ)^(-2:ℤ) : ℝ) = ((25939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2854 : ((((226121975741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25939 < q → q < 25943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25943).mp (by decide +kernel))) hgap
  have hprev := s2L_2853
  have hrat : ((226121975741 : ℚ) / 500000000000) ≤ ((452243949997 : ℚ) / 1000000000000) + (25943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121975741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243949997 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25943:ℚ)^(-2:ℤ) : ℝ) = ((25943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2855 : ((((226121976483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25943 < q → q < 25951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25951).mp (by decide +kernel))) hgap
  have hprev := s2L_2854
  have hrat : ((226121976483 : ℚ) / 500000000000) ≤ ((226121975741 : ℚ) / 500000000000) + (25951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121976483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121975741 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25951:ℚ)^(-2:ℤ) : ℝ) = ((25951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2856 : ((((28265247153 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25951 < q → q < 25969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25969).mp (by decide +kernel))) hgap
  have hprev := s2L_2855
  have hrat : ((28265247153 : ℚ) / 62500000000) ≤ ((226121976483 : ℚ) / 500000000000) + (25969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265247153 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121976483 : ℚ) / 500000000000) : ℚ) : ℝ) + ((25969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25969:ℚ)^(-2:ℤ) : ℝ) = ((25969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2857 : ((((452243955929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25969 < q → q < 25981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25981).mp (by decide +kernel))) hgap
  have hprev := s2L_2856
  have hrat : ((452243955929 : ℚ) / 1000000000000) ≤ ((28265247153 : ℚ) / 62500000000) + (25981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243955929 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265247153 : ℚ) / 62500000000) : ℚ) : ℝ) + ((25981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25981:ℚ)^(-2:ℤ) : ℝ) = ((25981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2858 : ((((14132623669 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25981 < q → q < 25997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25997).mp (by decide +kernel))) hgap
  have hprev := s2L_2857
  have hrat : ((14132623669 : ℚ) / 31250000000) ≤ ((452243955929 : ℚ) / 1000000000000) + (25997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132623669 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452243955929 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((25997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25997:ℚ)^(-2:ℤ) : ℝ) = ((25997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2859 : ((((452243958887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 25999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25997 < q → q < 25999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 25999).mp (by decide +kernel))) hgap
  have hprev := s2L_2858
  have hrat : ((452243958887 : ℚ) / 1000000000000) ≤ ((14132623669 : ℚ) / 31250000000) + (25999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243958887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132623669 : ℚ) / 31250000000) : ℚ) : ℝ) + ((25999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((25999:ℚ)^(-2:ℤ) : ℝ) = ((25999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2860 : ((((90448792073 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 25999 < q → q < 26003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26003).mp (by decide +kernel))) hgap
  have hprev := s2L_2859
  have hrat : ((90448792073 : ℚ) / 200000000000) ≤ ((452243958887 : ℚ) / 1000000000000) + (26003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448792073 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243958887 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26003:ℚ)^(-2:ℤ) : ℝ) = ((26003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2861 : ((((226121980921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26003 < q → q < 26017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26017).mp (by decide +kernel))) hgap
  have hprev := s2L_2860
  have hrat : ((226121980921 : ℚ) / 500000000000) ≤ ((90448792073 : ℚ) / 200000000000) + (26017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121980921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448792073 : ℚ) / 200000000000) : ℚ) : ℝ) + ((26017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26017:ℚ)^(-2:ℤ) : ℝ) = ((26017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2862 : ((((226121981659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26017 < q → q < 26021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26021).mp (by decide +kernel))) hgap
  have hprev := s2L_2861
  have hrat : ((226121981659 : ℚ) / 500000000000) ≤ ((226121980921 : ℚ) / 500000000000) + (26021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121981659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121980921 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26021:ℚ)^(-2:ℤ) : ℝ) = ((26021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2863 : ((((452243964793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26021 < q → q < 26029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26029).mp (by decide +kernel))) hgap
  have hprev := s2L_2862
  have hrat : ((452243964793 : ℚ) / 1000000000000) ≤ ((226121981659 : ℚ) / 500000000000) + (26029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243964793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121981659 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26029:ℚ)^(-2:ℤ) : ℝ) = ((26029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2864 : ((((452243966267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26029 < q → q < 26041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26041).mp (by decide +kernel))) hgap
  have hprev := s2L_2863
  have hrat : ((452243966267 : ℚ) / 1000000000000) ≤ ((452243964793 : ℚ) / 1000000000000) + (26041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243966267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243964793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26041:ℚ)^(-2:ℤ) : ℝ) = ((26041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2865 : ((((22612198387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26041 < q → q < 26053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26053).mp (by decide +kernel))) hgap
  have hprev := s2L_2864
  have hrat : ((22612198387 : ℚ) / 50000000000) ≤ ((452243966267 : ℚ) / 1000000000000) + (26053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612198387 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243966267 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26053:ℚ)^(-2:ℤ) : ℝ) = ((26053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2866 : ((((452243969209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26053 < q → q < 26083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26083).mp (by decide +kernel))) hgap
  have hprev := s2L_2865
  have hrat : ((452243969209 : ℚ) / 1000000000000) ≤ ((22612198387 : ℚ) / 50000000000) + (26083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243969209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612198387 : ℚ) / 50000000000) : ℚ) : ℝ) + ((26083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26083:ℚ)^(-2:ℤ) : ℝ) = ((26083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2867 : ((((452243970677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26083 < q → q < 26099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26099).mp (by decide +kernel))) hgap
  have hprev := s2L_2866
  have hrat : ((452243970677 : ℚ) / 1000000000000) ≤ ((452243969209 : ℚ) / 1000000000000) + (26099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243970677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243969209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26099:ℚ)^(-2:ℤ) : ℝ) = ((26099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2868 : ((((28265248259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26099 < q → q < 26107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26107).mp (by decide +kernel))) hgap
  have hprev := s2L_2867
  have hrat : ((28265248259 : ℚ) / 62500000000) ≤ ((452243970677 : ℚ) / 1000000000000) + (26107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265248259 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452243970677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26107:ℚ)^(-2:ℤ) : ℝ) = ((26107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2869 : ((((45224397361 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26107 < q → q < 26111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26111).mp (by decide +kernel))) hgap
  have hprev := s2L_2868
  have hrat : ((45224397361 : ℚ) / 100000000000) ≤ ((28265248259 : ℚ) / 62500000000) + (26111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224397361 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((28265248259 : ℚ) / 62500000000) : ℚ) : ℝ) + ((26111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26111:ℚ)^(-2:ℤ) : ℝ) = ((26111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2870 : ((((113060993769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26111 < q → q < 26113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26113).mp (by decide +kernel))) hgap
  have hprev := s2L_2869
  have hrat : ((113060993769 : ℚ) / 250000000000) ≤ ((45224397361 : ℚ) / 100000000000) + (26113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060993769 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45224397361 : ℚ) / 100000000000) : ℚ) : ℝ) + ((26113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26113:ℚ)^(-2:ℤ) : ℝ) = ((26113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2871 : ((((452243976541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26113 < q → q < 26119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26119).mp (by decide +kernel))) hgap
  have hprev := s2L_2870
  have hrat : ((452243976541 : ℚ) / 1000000000000) ≤ ((113060993769 : ℚ) / 250000000000) + (26119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243976541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060993769 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26119:ℚ)^(-2:ℤ) : ℝ) = ((26119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2872 : ((((113060994501 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26141, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26119 < q → q < 26141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26141).mp (by decide +kernel))) hgap
  have hprev := s2L_2871
  have hrat : ((113060994501 : ℚ) / 250000000000) ≤ ((452243976541 : ℚ) / 1000000000000) + (26141:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060994501 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243976541 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26141:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26141:ℚ)^(-2:ℤ) : ℝ) = ((26141:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2873 : ((((226121989733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26141 < q → q < 26153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26153).mp (by decide +kernel))) hgap
  have hprev := s2L_2872
  have hrat : ((226121989733 : ℚ) / 500000000000) ≤ ((113060994501 : ℚ) / 250000000000) + (26153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121989733 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060994501 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26153:ℚ)^(-2:ℤ) : ℝ) = ((26153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2874 : ((((452243980927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26153 < q → q < 26161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26161).mp (by decide +kernel))) hgap
  have hprev := s2L_2873
  have hrat : ((452243980927 : ℚ) / 1000000000000) ≤ ((226121989733 : ℚ) / 500000000000) + (26161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243980927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121989733 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26161:ℚ)^(-2:ℤ) : ℝ) = ((26161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2875 : ((((452243982387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26161 < q → q < 26171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26171).mp (by decide +kernel))) hgap
  have hprev := s2L_2874
  have hrat : ((452243982387 : ℚ) / 1000000000000) ≤ ((452243980927 : ℚ) / 1000000000000) + (26171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243982387 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243980927 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26171:ℚ)^(-2:ℤ) : ℝ) = ((26171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2876 : ((((226121991923 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26171 < q → q < 26177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26177).mp (by decide +kernel))) hgap
  have hprev := s2L_2875
  have hrat : ((226121991923 : ℚ) / 500000000000) ≤ ((452243982387 : ℚ) / 1000000000000) + (26177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121991923 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243982387 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26177:ℚ)^(-2:ℤ) : ℝ) = ((26177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2877 : ((((56530498163 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26177 < q → q < 26183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26183).mp (by decide +kernel))) hgap
  have hprev := s2L_2876
  have hrat : ((56530498163 : ℚ) / 125000000000) ≤ ((226121991923 : ℚ) / 500000000000) + (26183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530498163 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121991923 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26183:ℚ)^(-2:ℤ) : ℝ) = ((26183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2878 : ((((226121993381 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26183 < q → q < 26189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26189).mp (by decide +kernel))) hgap
  have hprev := s2L_2877
  have hrat : ((226121993381 : ℚ) / 500000000000) ≤ ((56530498163 : ℚ) / 125000000000) + (26189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121993381 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530498163 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26189:ℚ)^(-2:ℤ) : ℝ) = ((26189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2879 : ((((226121994109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26189 < q → q < 26203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26203).mp (by decide +kernel))) hgap
  have hprev := s2L_2878
  have hrat : ((226121994109 : ℚ) / 500000000000) ≤ ((226121993381 : ℚ) / 500000000000) + (26203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121994109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121993381 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26203:ℚ)^(-2:ℤ) : ℝ) = ((26203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2880 : ((((452243989673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26203 < q → q < 26209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26209).mp (by decide +kernel))) hgap
  have hprev := s2L_2879
  have hrat : ((452243989673 : ℚ) / 1000000000000) ≤ ((226121994109 : ℚ) / 500000000000) + (26209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243989673 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121994109 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26209:ℚ)^(-2:ℤ) : ℝ) = ((26209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2881 : ((((226121995563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26209 < q → q < 26227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26227).mp (by decide +kernel))) hgap
  have hprev := s2L_2880
  have hrat : ((226121995563 : ℚ) / 500000000000) ≤ ((452243989673 : ℚ) / 1000000000000) + (26227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121995563 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243989673 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26227:ℚ)^(-2:ℤ) : ℝ) = ((26227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2882 : ((((226121996289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26227 < q → q < 26237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26237).mp (by decide +kernel))) hgap
  have hprev := s2L_2881
  have hrat : ((226121996289 : ℚ) / 500000000000) ≤ ((226121995563 : ℚ) / 500000000000) + (26237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121996289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121995563 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26237:ℚ)^(-2:ℤ) : ℝ) = ((26237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2883 : ((((452243994029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26237 < q → q < 26249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26249).mp (by decide +kernel))) hgap
  have hprev := s2L_2882
  have hrat : ((452243994029 : ℚ) / 1000000000000) ≤ ((226121996289 : ℚ) / 500000000000) + (26249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243994029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121996289 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26249:ℚ)^(-2:ℤ) : ℝ) = ((26249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2884 : ((((11306099887 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26249 < q → q < 26251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26251).mp (by decide +kernel))) hgap
  have hprev := s2L_2883
  have hrat : ((11306099887 : ℚ) / 25000000000) ≤ ((452243994029 : ℚ) / 1000000000000) + (26251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306099887 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452243994029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26251:ℚ)^(-2:ℤ) : ℝ) = ((26251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2885 : ((((45224399693 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26251 < q → q < 26261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26261).mp (by decide +kernel))) hgap
  have hprev := s2L_2884
  have hrat : ((45224399693 : ℚ) / 100000000000) ≤ ((11306099887 : ℚ) / 25000000000) + (26261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224399693 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((11306099887 : ℚ) / 25000000000) : ℚ) : ℝ) + ((26261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26261:ℚ)^(-2:ℤ) : ℝ) = ((26261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2886 : ((((452243998379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26261 < q → q < 26263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26263).mp (by decide +kernel))) hgap
  have hprev := s2L_2885
  have hrat : ((452243998379 : ℚ) / 1000000000000) ≤ ((45224399693 : ℚ) / 100000000000) + (26263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243998379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224399693 : ℚ) / 100000000000) : ℚ) : ℝ) + ((26263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26263:ℚ)^(-2:ℤ) : ℝ) = ((26263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2887 : ((((113060999957 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26263 < q → q < 26267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26267).mp (by decide +kernel))) hgap
  have hprev := s2L_2886
  have hrat : ((113060999957 : ℚ) / 250000000000) ≤ ((452243998379 : ℚ) / 1000000000000) + (26267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060999957 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243998379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26267:ℚ)^(-2:ℤ) : ℝ) = ((26267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2888 : ((((226122000637 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26267 < q → q < 26293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26293).mp (by decide +kernel))) hgap
  have hprev := s2L_2887
  have hrat : ((226122000637 : ℚ) / 500000000000) ≤ ((113060999957 : ℚ) / 250000000000) + (26293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122000637 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060999957 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26293:ℚ)^(-2:ℤ) : ℝ) = ((26293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2889 : ((((2826525017 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26293 < q → q < 26297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26297).mp (by decide +kernel))) hgap
  have hprev := s2L_2888
  have hrat : ((2826525017 : ℚ) / 6250000000) ≤ ((226122000637 : ℚ) / 500000000000) + (26297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2826525017 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((226122000637 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26297:ℚ)^(-2:ℤ) : ℝ) = ((26297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2890 : ((((113061001041 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26297 < q → q < 26309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26309).mp (by decide +kernel))) hgap
  have hprev := s2L_2889
  have hrat : ((113061001041 : ℚ) / 250000000000) ≤ ((2826525017 : ℚ) / 6250000000) + (26309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061001041 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2826525017 : ℚ) / 6250000000) : ℚ) : ℝ) + ((26309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26309:ℚ)^(-2:ℤ) : ℝ) = ((26309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2891 : ((((452244005607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26309 < q → q < 26317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26317).mp (by decide +kernel))) hgap
  have hprev := s2L_2890
  have hrat : ((452244005607 : ℚ) / 1000000000000) ≤ ((113061001041 : ℚ) / 250000000000) + (26317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244005607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061001041 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26317:ℚ)^(-2:ℤ) : ℝ) = ((26317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2892 : ((((9044880141 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26317 < q → q < 26321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26321).mp (by decide +kernel))) hgap
  have hprev := s2L_2891
  have hrat : ((9044880141 : ℚ) / 20000000000) ≤ ((452244005607 : ℚ) / 1000000000000) + (26321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044880141 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452244005607 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26321:ℚ)^(-2:ℤ) : ℝ) = ((26321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2893 : ((((452244008491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26321 < q → q < 26339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26339).mp (by decide +kernel))) hgap
  have hprev := s2L_2892
  have hrat : ((452244008491 : ℚ) / 1000000000000) ≤ ((9044880141 : ℚ) / 20000000000) + (26339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244008491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044880141 : ℚ) / 20000000000) : ℚ) : ℝ) + ((26339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26339:ℚ)^(-2:ℤ) : ℝ) = ((26339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2894 : ((((452244009931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26339 < q → q < 26347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26347).mp (by decide +kernel))) hgap
  have hprev := s2L_2893
  have hrat : ((452244009931 : ℚ) / 1000000000000) ≤ ((452244008491 : ℚ) / 1000000000000) + (26347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244009931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244008491 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26347:ℚ)^(-2:ℤ) : ℝ) = ((26347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2895 : ((((45224401137 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26347 < q → q < 26357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26357).mp (by decide +kernel))) hgap
  have hprev := s2L_2894
  have hrat : ((45224401137 : ℚ) / 100000000000) ≤ ((452244009931 : ℚ) / 1000000000000) + (26357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224401137 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452244009931 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26357:ℚ)^(-2:ℤ) : ℝ) = ((26357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2896 : ((((452244012807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26357 < q → q < 26371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26371).mp (by decide +kernel))) hgap
  have hprev := s2L_2895
  have hrat : ((452244012807 : ℚ) / 1000000000000) ≤ ((45224401137 : ℚ) / 100000000000) + (26371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244012807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224401137 : ℚ) / 100000000000) : ℚ) : ℝ) + ((26371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26371:ℚ)^(-2:ℤ) : ℝ) = ((26371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2897 : ((((452244014243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26371 < q → q < 26387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26387).mp (by decide +kernel))) hgap
  have hprev := s2L_2896
  have hrat : ((452244014243 : ℚ) / 1000000000000) ≤ ((452244012807 : ℚ) / 1000000000000) + (26387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244014243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244012807 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26387:ℚ)^(-2:ℤ) : ℝ) = ((26387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2898 : ((((226122007839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26387 < q → q < 26393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26393).mp (by decide +kernel))) hgap
  have hprev := s2L_2897
  have hrat : ((226122007839 : ℚ) / 500000000000) ≤ ((452244014243 : ℚ) / 1000000000000) + (26393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122007839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244014243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26393:ℚ)^(-2:ℤ) : ℝ) = ((26393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2899 : ((((56530502139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26393 < q → q < 26399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26399).mp (by decide +kernel))) hgap
  have hprev := s2L_2898
  have hrat : ((56530502139 : ℚ) / 125000000000) ≤ ((226122007839 : ℚ) / 500000000000) + (26399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530502139 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122007839 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26399:ℚ)^(-2:ℤ) : ℝ) = ((26399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2900 : ((((226122009273 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26399 < q → q < 26407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26407).mp (by decide +kernel))) hgap
  have hprev := s2L_2899
  have hrat : ((226122009273 : ℚ) / 500000000000) ≤ ((56530502139 : ℚ) / 125000000000) + (26407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122009273 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530502139 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26407:ℚ)^(-2:ℤ) : ℝ) = ((26407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2901 : ((((226122009989 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26407 < q → q < 26417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26417).mp (by decide +kernel))) hgap
  have hprev := s2L_2900
  have hrat : ((226122009989 : ℚ) / 500000000000) ≤ ((226122009273 : ℚ) / 500000000000) + (26417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122009989 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122009273 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26417:ℚ)^(-2:ℤ) : ℝ) = ((26417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2902 : ((((45224402141 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26417 < q → q < 26423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26423).mp (by decide +kernel))) hgap
  have hprev := s2L_2901
  have hrat : ((45224402141 : ℚ) / 100000000000) ≤ ((226122009989 : ℚ) / 500000000000) + (26423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224402141 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226122009989 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26423:ℚ)^(-2:ℤ) : ℝ) = ((26423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2903 : ((((452244022841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26423 < q → q < 26431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26431).mp (by decide +kernel))) hgap
  have hprev := s2L_2902
  have hrat : ((452244022841 : ℚ) / 1000000000000) ≤ ((45224402141 : ℚ) / 100000000000) + (26431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244022841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224402141 : ℚ) / 100000000000) : ℚ) : ℝ) + ((26431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26431:ℚ)^(-2:ℤ) : ℝ) = ((26431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2904 : ((((452244024271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26431 < q → q < 26437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26437).mp (by decide +kernel))) hgap
  have hprev := s2L_2903
  have hrat : ((452244024271 : ℚ) / 1000000000000) ≤ ((452244022841 : ℚ) / 1000000000000) + (26437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244024271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244022841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26437:ℚ)^(-2:ℤ) : ℝ) = ((26437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2905 : ((((4522440257 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26437 < q → q < 26449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26449).mp (by decide +kernel))) hgap
  have hprev := s2L_2904
  have hrat : ((4522440257 : ℚ) / 10000000000) ≤ ((452244024271 : ℚ) / 1000000000000) + (26449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522440257 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452244024271 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26449:ℚ)^(-2:ℤ) : ℝ) = ((26449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2906 : ((((56530503391 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26449 < q → q < 26459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26459).mp (by decide +kernel))) hgap
  have hprev := s2L_2905
  have hrat : ((56530503391 : ℚ) / 125000000000) ≤ ((4522440257 : ℚ) / 10000000000) + (26459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530503391 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4522440257 : ℚ) / 10000000000) : ℚ) : ℝ) + ((26459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26459:ℚ)^(-2:ℤ) : ℝ) = ((26459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2907 : ((((226122014277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26459 < q → q < 26479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26479).mp (by decide +kernel))) hgap
  have hprev := s2L_2906
  have hrat : ((226122014277 : ℚ) / 500000000000) ≤ ((56530503391 : ℚ) / 125000000000) + (26479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122014277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530503391 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26479:ℚ)^(-2:ℤ) : ℝ) = ((26479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2908 : ((((452244029979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26479 < q → q < 26489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26489).mp (by decide +kernel))) hgap
  have hprev := s2L_2907
  have hrat : ((452244029979 : ℚ) / 1000000000000) ≤ ((226122014277 : ℚ) / 500000000000) + (26489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244029979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122014277 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26489:ℚ)^(-2:ℤ) : ℝ) = ((26489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2909 : ((((452244031403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26489 < q → q < 26497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26497).mp (by decide +kernel))) hgap
  have hprev := s2L_2908
  have hrat : ((452244031403 : ℚ) / 1000000000000) ≤ ((452244029979 : ℚ) / 1000000000000) + (26497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244031403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244029979 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26497:ℚ)^(-2:ℤ) : ℝ) = ((26497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2910 : ((((226122016413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26497 < q → q < 26501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26501).mp (by decide +kernel))) hgap
  have hprev := s2L_2909
  have hrat : ((226122016413 : ℚ) / 500000000000) ≤ ((452244031403 : ℚ) / 1000000000000) + (26501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122016413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244031403 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26501:ℚ)^(-2:ℤ) : ℝ) = ((26501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2911 : ((((56530504281 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26501 < q → q < 26513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26513).mp (by decide +kernel))) hgap
  have hprev := s2L_2910
  have hrat : ((56530504281 : ℚ) / 125000000000) ≤ ((226122016413 : ℚ) / 500000000000) + (26513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530504281 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122016413 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26513:ℚ)^(-2:ℤ) : ℝ) = ((26513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2912 : ((((452244035667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26513 < q → q < 26539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26539).mp (by decide +kernel))) hgap
  have hprev := s2L_2911
  have hrat : ((452244035667 : ℚ) / 1000000000000) ≤ ((56530504281 : ℚ) / 125000000000) + (26539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244035667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530504281 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26539:ℚ)^(-2:ℤ) : ℝ) = ((26539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2913 : ((((113061009271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26539 < q → q < 26557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26557).mp (by decide +kernel))) hgap
  have hprev := s2L_2912
  have hrat : ((113061009271 : ℚ) / 250000000000) ≤ ((452244035667 : ℚ) / 1000000000000) + (26557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061009271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244035667 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26557:ℚ)^(-2:ℤ) : ℝ) = ((26557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2914 : ((((452244038501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26557 < q → q < 26561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26561).mp (by decide +kernel))) hgap
  have hprev := s2L_2913
  have hrat : ((452244038501 : ℚ) / 1000000000000) ≤ ((113061009271 : ℚ) / 250000000000) + (26561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244038501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061009271 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26561:ℚ)^(-2:ℤ) : ℝ) = ((26561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2915 : ((((452244039917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26561 < q → q < 26573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26573).mp (by decide +kernel))) hgap
  have hprev := s2L_2914
  have hrat : ((452244039917 : ℚ) / 1000000000000) ≤ ((452244038501 : ℚ) / 1000000000000) + (26573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244039917 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244038501 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26573:ℚ)^(-2:ℤ) : ℝ) = ((26573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2916 : ((((452244041331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26573 < q → q < 26591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26591).mp (by decide +kernel))) hgap
  have hprev := s2L_2915
  have hrat : ((452244041331 : ℚ) / 1000000000000) ≤ ((452244039917 : ℚ) / 1000000000000) + (26591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244041331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244039917 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26591:ℚ)^(-2:ℤ) : ℝ) = ((26591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2917 : ((((56530505343 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26591 < q → q < 26597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26597).mp (by decide +kernel))) hgap
  have hprev := s2L_2916
  have hrat : ((56530505343 : ℚ) / 125000000000) ≤ ((452244041331 : ℚ) / 1000000000000) + (26597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530505343 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244041331 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26597:ℚ)^(-2:ℤ) : ℝ) = ((26597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2918 : ((((226122022077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26597 < q → q < 26627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26627).mp (by decide +kernel))) hgap
  have hprev := s2L_2917
  have hrat : ((226122022077 : ℚ) / 500000000000) ≤ ((56530505343 : ℚ) / 125000000000) + (26627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122022077 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530505343 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26627:ℚ)^(-2:ℤ) : ℝ) = ((26627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2919 : ((((452244045563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26627 < q → q < 26633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26633).mp (by decide +kernel))) hgap
  have hprev := s2L_2918
  have hrat : ((452244045563 : ℚ) / 1000000000000) ≤ ((226122022077 : ℚ) / 500000000000) + (26633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244045563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122022077 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26633:ℚ)^(-2:ℤ) : ℝ) = ((26633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2920 : ((((452244046971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26633 < q → q < 26641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26641).mp (by decide +kernel))) hgap
  have hprev := s2L_2919
  have hrat : ((452244046971 : ℚ) / 1000000000000) ≤ ((452244045563 : ℚ) / 1000000000000) + (26641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244046971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244045563 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26641:ℚ)^(-2:ℤ) : ℝ) = ((26641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2921 : ((((452244048379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26641 < q → q < 26647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26647).mp (by decide +kernel))) hgap
  have hprev := s2L_2920
  have hrat : ((452244048379 : ℚ) / 1000000000000) ≤ ((452244046971 : ℚ) / 1000000000000) + (26647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244048379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244046971 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26647:ℚ)^(-2:ℤ) : ℝ) = ((26647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2922 : ((((90448809957 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26647 < q → q < 26669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26669).mp (by decide +kernel))) hgap
  have hprev := s2L_2921
  have hrat : ((90448809957 : ℚ) / 200000000000) ≤ ((452244048379 : ℚ) / 1000000000000) + (26669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448809957 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244048379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26669:ℚ)^(-2:ℤ) : ℝ) = ((26669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2923 : ((((452244051189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26669 < q → q < 26681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26681).mp (by decide +kernel))) hgap
  have hprev := s2L_2922
  have hrat : ((452244051189 : ℚ) / 1000000000000) ≤ ((90448809957 : ℚ) / 200000000000) + (26681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244051189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448809957 : ℚ) / 200000000000) : ℚ) : ℝ) + ((26681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26681:ℚ)^(-2:ℤ) : ℝ) = ((26681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2924 : ((((452244052593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26681 < q → q < 26683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26683).mp (by decide +kernel))) hgap
  have hprev := s2L_2923
  have hrat : ((452244052593 : ℚ) / 1000000000000) ≤ ((452244051189 : ℚ) / 1000000000000) + (26683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244052593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244051189 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26683:ℚ)^(-2:ℤ) : ℝ) = ((26683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2925 : ((((452244053997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26683 < q → q < 26687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26687).mp (by decide +kernel))) hgap
  have hprev := s2L_2924
  have hrat : ((452244053997 : ℚ) / 1000000000000) ≤ ((452244052593 : ℚ) / 1000000000000) + (26687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244053997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244052593 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26687:ℚ)^(-2:ℤ) : ℝ) = ((26687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2926 : ((((2261220277 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26687 < q → q < 26693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26693).mp (by decide +kernel))) hgap
  have hprev := s2L_2925
  have hrat : ((2261220277 : ℚ) / 5000000000) ≤ ((452244053997 : ℚ) / 1000000000000) + (26693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261220277 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452244053997 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26693:ℚ)^(-2:ℤ) : ℝ) = ((26693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2927 : ((((226122028401 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26693 < q → q < 26699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26699).mp (by decide +kernel))) hgap
  have hprev := s2L_2926
  have hrat : ((226122028401 : ℚ) / 500000000000) ≤ ((2261220277 : ℚ) / 5000000000) + (26699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122028401 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((2261220277 : ℚ) / 5000000000) : ℚ) : ℝ) + ((26699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26699:ℚ)^(-2:ℤ) : ℝ) = ((26699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2928 : ((((113061014551 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26699 < q → q < 26701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26701).mp (by decide +kernel))) hgap
  have hprev := s2L_2927
  have hrat : ((113061014551 : ℚ) / 250000000000) ≤ ((226122028401 : ℚ) / 500000000000) + (26701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061014551 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122028401 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26701:ℚ)^(-2:ℤ) : ℝ) = ((26701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2929 : ((((90448811921 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26701 < q → q < 26711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26711).mp (by decide +kernel))) hgap
  have hprev := s2L_2928
  have hrat : ((90448811921 : ℚ) / 200000000000) ≤ ((113061014551 : ℚ) / 250000000000) + (26711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448811921 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113061014551 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26711:ℚ)^(-2:ℤ) : ℝ) = ((26711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2930 : ((((226122030503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26711 < q → q < 26713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26713).mp (by decide +kernel))) hgap
  have hprev := s2L_2929
  have hrat : ((226122030503 : ℚ) / 500000000000) ≤ ((90448811921 : ℚ) / 200000000000) + (26713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122030503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448811921 : ℚ) / 200000000000) : ℚ) : ℝ) + ((26713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26713:ℚ)^(-2:ℤ) : ℝ) = ((26713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2931 : ((((226122031203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26713 < q → q < 26717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26717).mp (by decide +kernel))) hgap
  have hprev := s2L_2930
  have hrat : ((226122031203 : ℚ) / 500000000000) ≤ ((226122030503 : ℚ) / 500000000000) + (26717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122031203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122030503 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26717:ℚ)^(-2:ℤ) : ℝ) = ((26717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2932 : ((((226122031903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26717 < q → q < 26723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26723).mp (by decide +kernel))) hgap
  have hprev := s2L_2931
  have hrat : ((226122031903 : ℚ) / 500000000000) ≤ ((226122031203 : ℚ) / 500000000000) + (26723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122031903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122031203 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26723:ℚ)^(-2:ℤ) : ℝ) = ((26723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2933 : ((((90448813041 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26723 < q → q < 26729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26729).mp (by decide +kernel))) hgap
  have hprev := s2L_2932
  have hrat : ((90448813041 : ℚ) / 200000000000) ≤ ((226122031903 : ℚ) / 500000000000) + (26729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448813041 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226122031903 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26729:ℚ)^(-2:ℤ) : ℝ) = ((26729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2934 : ((((113061016651 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26729 < q → q < 26731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26731).mp (by decide +kernel))) hgap
  have hprev := s2L_2933
  have hrat : ((113061016651 : ℚ) / 250000000000) ≤ ((90448813041 : ℚ) / 200000000000) + (26731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061016651 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448813041 : ℚ) / 200000000000) : ℚ) : ℝ) + ((26731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26731:ℚ)^(-2:ℤ) : ℝ) = ((26731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2935 : ((((226122034001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26731 < q → q < 26737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26737).mp (by decide +kernel))) hgap
  have hprev := s2L_2934
  have hrat : ((226122034001 : ℚ) / 500000000000) ≤ ((113061016651 : ℚ) / 250000000000) + (26737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122034001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061016651 : ℚ) / 250000000000) : ℚ) : ℝ) + ((26737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26737:ℚ)^(-2:ℤ) : ℝ) = ((26737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2936 : ((((226122034699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26737 < q → q < 26759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26759).mp (by decide +kernel))) hgap
  have hprev := s2L_2935
  have hrat : ((226122034699 : ℚ) / 500000000000) ≤ ((226122034001 : ℚ) / 500000000000) + (26759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122034699 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122034001 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26759:ℚ)^(-2:ℤ) : ℝ) = ((26759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2937 : ((((56530508849 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26759 < q → q < 26777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26777).mp (by decide +kernel))) hgap
  have hprev := s2L_2936
  have hrat : ((56530508849 : ℚ) / 125000000000) ≤ ((226122034699 : ℚ) / 500000000000) + (26777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530508849 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122034699 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26777:ℚ)^(-2:ℤ) : ℝ) = ((26777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2938 : ((((226122036093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26777 < q → q < 26783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26783).mp (by decide +kernel))) hgap
  have hprev := s2L_2937
  have hrat : ((226122036093 : ℚ) / 500000000000) ≤ ((56530508849 : ℚ) / 125000000000) + (26783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122036093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530508849 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26783:ℚ)^(-2:ℤ) : ℝ) = ((26783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2939 : ((((226122036789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26783 < q → q < 26801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26801).mp (by decide +kernel))) hgap
  have hprev := s2L_2938
  have hrat : ((226122036789 : ℚ) / 500000000000) ≤ ((226122036093 : ℚ) / 500000000000) + (26801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122036789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122036093 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26801:ℚ)^(-2:ℤ) : ℝ) = ((26801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2940 : ((((56530509371 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26801 < q → q < 26813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26813).mp (by decide +kernel))) hgap
  have hprev := s2L_2939
  have hrat : ((56530509371 : ℚ) / 125000000000) ≤ ((226122036789 : ℚ) / 500000000000) + (26813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530509371 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122036789 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26813:ℚ)^(-2:ℤ) : ℝ) = ((26813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2941 : ((((226122038179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26813 < q → q < 26821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26821).mp (by decide +kernel))) hgap
  have hprev := s2L_2940
  have hrat : ((226122038179 : ℚ) / 500000000000) ≤ ((56530509371 : ℚ) / 125000000000) + (26821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122038179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530509371 : ℚ) / 125000000000) : ℚ) : ℝ) + ((26821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26821:ℚ)^(-2:ℤ) : ℝ) = ((26821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2942 : ((((226122038873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26821 < q → q < 26833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26833).mp (by decide +kernel))) hgap
  have hprev := s2L_2941
  have hrat : ((226122038873 : ℚ) / 500000000000) ≤ ((226122038179 : ℚ) / 500000000000) + (26833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122038873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122038179 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26833:ℚ)^(-2:ℤ) : ℝ) = ((26833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2943 : ((((226122039567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26833 < q → q < 26839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26839).mp (by decide +kernel))) hgap
  have hprev := s2L_2942
  have hrat : ((226122039567 : ℚ) / 500000000000) ≤ ((226122038873 : ℚ) / 500000000000) + (26839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122039567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122038873 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26839:ℚ)^(-2:ℤ) : ℝ) = ((26839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2944 : ((((452244080521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26849, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26839 < q → q < 26849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26849).mp (by decide +kernel))) hgap
  have hprev := s2L_2943
  have hrat : ((452244080521 : ℚ) / 1000000000000) ≤ ((226122039567 : ℚ) / 500000000000) + (26849:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244080521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122039567 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26849:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26849:ℚ)^(-2:ℤ) : ℝ) = ((26849:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2945 : ((((226122040953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26849 < q → q < 26861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26861).mp (by decide +kernel))) hgap
  have hprev := s2L_2944
  have hrat : ((226122040953 : ℚ) / 500000000000) ≤ ((452244080521 : ℚ) / 1000000000000) + (26861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122040953 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244080521 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26861:ℚ)^(-2:ℤ) : ℝ) = ((26861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2946 : ((((452244083291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26861 < q → q < 26863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26863).mp (by decide +kernel))) hgap
  have hprev := s2L_2945
  have hrat : ((452244083291 : ℚ) / 1000000000000) ≤ ((226122040953 : ℚ) / 500000000000) + (26863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244083291 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122040953 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26863:ℚ)^(-2:ℤ) : ℝ) = ((26863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2947 : ((((18089763387 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26863 < q → q < 26879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26879).mp (by decide +kernel))) hgap
  have hprev := s2L_2946
  have hrat : ((18089763387 : ℚ) / 40000000000) ≤ ((452244083291 : ℚ) / 1000000000000) + (26879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089763387 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244083291 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26879:ℚ)^(-2:ℤ) : ℝ) = ((26879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2948 : ((((226122043029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26879 < q → q < 26881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26881).mp (by decide +kernel))) hgap
  have hprev := s2L_2947
  have hrat : ((226122043029 : ℚ) / 500000000000) ≤ ((18089763387 : ℚ) / 40000000000) + (26881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122043029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089763387 : ℚ) / 40000000000) : ℚ) : ℝ) + ((26881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26881:ℚ)^(-2:ℤ) : ℝ) = ((26881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2949 : ((((5653051093 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26891, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26881 < q → q < 26891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26891).mp (by decide +kernel))) hgap
  have hprev := s2L_2948
  have hrat : ((5653051093 : ℚ) / 12500000000) ≤ ((226122043029 : ℚ) / 500000000000) + (26891:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653051093 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226122043029 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26891:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26891:ℚ)^(-2:ℤ) : ℝ) = ((26891:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2950 : ((((226122044411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26891 < q → q < 26893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26893).mp (by decide +kernel))) hgap
  have hprev := s2L_2949
  have hrat : ((226122044411 : ℚ) / 500000000000) ≤ ((5653051093 : ℚ) / 12500000000) + (26893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122044411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((5653051093 : ℚ) / 12500000000) : ℚ) : ℝ) + ((26893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26893:ℚ)^(-2:ℤ) : ℝ) = ((26893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2951 : ((((452244090203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26893 < q → q < 26903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26903).mp (by decide +kernel))) hgap
  have hprev := s2L_2950
  have hrat : ((452244090203 : ℚ) / 1000000000000) ≤ ((226122044411 : ℚ) / 500000000000) + (26903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244090203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122044411 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26903:ℚ)^(-2:ℤ) : ℝ) = ((26903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2952 : ((((226122045791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26903 < q → q < 26921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26921).mp (by decide +kernel))) hgap
  have hprev := s2L_2951
  have hrat : ((226122045791 : ℚ) / 500000000000) ≤ ((452244090203 : ℚ) / 1000000000000) + (26921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122045791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244090203 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26921:ℚ)^(-2:ℤ) : ℝ) = ((26921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2953 : ((((452244092961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26921 < q → q < 26927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26927).mp (by decide +kernel))) hgap
  have hprev := s2L_2952
  have hrat : ((452244092961 : ℚ) / 1000000000000) ≤ ((226122045791 : ℚ) / 500000000000) + (26927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244092961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122045791 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26927:ℚ)^(-2:ℤ) : ℝ) = ((26927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2954 : ((((226122047169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26927 < q → q < 26947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26947).mp (by decide +kernel))) hgap
  have hprev := s2L_2953
  have hrat : ((226122047169 : ℚ) / 500000000000) ≤ ((452244092961 : ℚ) / 1000000000000) + (26947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122047169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244092961 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26947:ℚ)^(-2:ℤ) : ℝ) = ((26947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2955 : ((((226122047857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26947 < q → q < 26951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26951).mp (by decide +kernel))) hgap
  have hprev := s2L_2954
  have hrat : ((226122047857 : ℚ) / 500000000000) ≤ ((226122047169 : ℚ) / 500000000000) + (26951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122047857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122047169 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26951:ℚ)^(-2:ℤ) : ℝ) = ((26951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2956 : ((((45224409709 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26951 < q → q < 26953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26953).mp (by decide +kernel))) hgap
  have hprev := s2L_2955
  have hrat : ((45224409709 : ℚ) / 100000000000) ≤ ((226122047857 : ℚ) / 500000000000) + (26953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224409709 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226122047857 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26953:ℚ)^(-2:ℤ) : ℝ) = ((26953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2957 : ((((90448819693 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26953 < q → q < 26959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26959).mp (by decide +kernel))) hgap
  have hprev := s2L_2956
  have hrat : ((90448819693 : ℚ) / 200000000000) ≤ ((45224409709 : ℚ) / 100000000000) + (26959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448819693 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45224409709 : ℚ) / 100000000000) : ℚ) : ℝ) + ((26959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26959:ℚ)^(-2:ℤ) : ℝ) = ((26959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2958 : ((((226122049919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26959 < q → q < 26981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26981).mp (by decide +kernel))) hgap
  have hprev := s2L_2957
  have hrat : ((226122049919 : ℚ) / 500000000000) ≤ ((90448819693 : ℚ) / 200000000000) + (26981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122049919 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448819693 : ℚ) / 200000000000) : ℚ) : ℝ) + ((26981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26981:ℚ)^(-2:ℤ) : ℝ) = ((26981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2959 : ((((452244101211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26981 < q → q < 26987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26987).mp (by decide +kernel))) hgap
  have hprev := s2L_2958
  have hrat : ((452244101211 : ℚ) / 1000000000000) ≤ ((226122049919 : ℚ) / 500000000000) + (26987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244101211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122049919 : ℚ) / 500000000000) : ℚ) : ℝ) + ((26987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26987:ℚ)^(-2:ℤ) : ℝ) = ((26987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2960 : ((((452244102583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 26993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26987 < q → q < 26993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 26993).mp (by decide +kernel))) hgap
  have hprev := s2L_2959
  have hrat : ((452244102583 : ℚ) / 1000000000000) ≤ ((452244101211 : ℚ) / 1000000000000) + (26993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244102583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244101211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((26993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((26993:ℚ)^(-2:ℤ) : ℝ) = ((26993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2961 : ((((452244103953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 26993 < q → q < 27011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27011).mp (by decide +kernel))) hgap
  have hprev := s2L_2960
  have hrat : ((452244103953 : ℚ) / 1000000000000) ≤ ((452244102583 : ℚ) / 1000000000000) + (27011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244103953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244102583 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27011:ℚ)^(-2:ℤ) : ℝ) = ((27011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2962 : ((((452244105323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27011 < q → q < 27017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27017).mp (by decide +kernel))) hgap
  have hprev := s2L_2961
  have hrat : ((452244105323 : ℚ) / 1000000000000) ≤ ((452244103953 : ℚ) / 1000000000000) + (27017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244105323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244103953 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27017:ℚ)^(-2:ℤ) : ℝ) = ((27017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2963 : ((((452244106691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27017 < q → q < 27031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27031).mp (by decide +kernel))) hgap
  have hprev := s2L_2962
  have hrat : ((452244106691 : ℚ) / 1000000000000) ≤ ((452244105323 : ℚ) / 1000000000000) + (27031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244106691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244105323 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27031:ℚ)^(-2:ℤ) : ℝ) = ((27031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2964 : ((((226122054029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27031 < q → q < 27043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27043).mp (by decide +kernel))) hgap
  have hprev := s2L_2963
  have hrat : ((226122054029 : ℚ) / 500000000000) ≤ ((452244106691 : ℚ) / 1000000000000) + (27043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122054029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244106691 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27043:ℚ)^(-2:ℤ) : ℝ) = ((27043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2965 : ((((452244109423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27043 < q → q < 27059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27059).mp (by decide +kernel))) hgap
  have hprev := s2L_2964
  have hrat : ((452244109423 : ℚ) / 1000000000000) ≤ ((226122054029 : ℚ) / 500000000000) + (27059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244109423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122054029 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27059:ℚ)^(-2:ℤ) : ℝ) = ((27059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2966 : ((((113061027697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27059 < q → q < 27061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27061).mp (by decide +kernel))) hgap
  have hprev := s2L_2965
  have hrat : ((113061027697 : ℚ) / 250000000000) ≤ ((452244109423 : ℚ) / 1000000000000) + (27061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061027697 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244109423 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27061:ℚ)^(-2:ℤ) : ℝ) = ((27061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2967 : ((((56530514019 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27061 < q → q < 27067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27067).mp (by decide +kernel))) hgap
  have hprev := s2L_2966
  have hrat : ((56530514019 : ℚ) / 125000000000) ≤ ((113061027697 : ℚ) / 250000000000) + (27067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530514019 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113061027697 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27067:ℚ)^(-2:ℤ) : ℝ) = ((27067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2968 : ((((113061028379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27067 < q → q < 27073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27073).mp (by decide +kernel))) hgap
  have hprev := s2L_2967
  have hrat : ((113061028379 : ℚ) / 250000000000) ≤ ((56530514019 : ℚ) / 125000000000) + (27073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061028379 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530514019 : ℚ) / 125000000000) : ℚ) : ℝ) + ((27073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27073:ℚ)^(-2:ℤ) : ℝ) = ((27073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2969 : ((((452244114879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27073 < q → q < 27077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27077).mp (by decide +kernel))) hgap
  have hprev := s2L_2968
  have hrat : ((452244114879 : ℚ) / 1000000000000) ≤ ((113061028379 : ℚ) / 250000000000) + (27077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244114879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061028379 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27077:ℚ)^(-2:ℤ) : ℝ) = ((27077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2970 : ((((452244116241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27077 < q → q < 27091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27091).mp (by decide +kernel))) hgap
  have hprev := s2L_2969
  have hrat : ((452244116241 : ℚ) / 1000000000000) ≤ ((452244114879 : ℚ) / 1000000000000) + (27091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244116241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244114879 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27091:ℚ)^(-2:ℤ) : ℝ) = ((27091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2971 : ((((226122058801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27091 < q → q < 27103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27103).mp (by decide +kernel))) hgap
  have hprev := s2L_2970
  have hrat : ((226122058801 : ℚ) / 500000000000) ≤ ((452244116241 : ℚ) / 1000000000000) + (27103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122058801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244116241 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27103:ℚ)^(-2:ℤ) : ℝ) = ((27103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2972 : ((((226122059481 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27103 < q → q < 27107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27107).mp (by decide +kernel))) hgap
  have hprev := s2L_2971
  have hrat : ((226122059481 : ℚ) / 500000000000) ≤ ((226122058801 : ℚ) / 500000000000) + (27107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122059481 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122058801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27107:ℚ)^(-2:ℤ) : ℝ) = ((27107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2973 : ((((226122060161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27107 < q → q < 27109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27109).mp (by decide +kernel))) hgap
  have hprev := s2L_2972
  have hrat : ((226122060161 : ℚ) / 500000000000) ≤ ((226122059481 : ℚ) / 500000000000) + (27109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122060161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122059481 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27109:ℚ)^(-2:ℤ) : ℝ) = ((27109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2974 : ((((5653051521 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27109 < q → q < 27127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27127).mp (by decide +kernel))) hgap
  have hprev := s2L_2973
  have hrat : ((5653051521 : ℚ) / 12500000000) ≤ ((226122060161 : ℚ) / 500000000000) + (27127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653051521 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226122060161 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27127:ℚ)^(-2:ℤ) : ℝ) = ((27127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2975 : ((((452244123037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27127 < q → q < 27143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27143).mp (by decide +kernel))) hgap
  have hprev := s2L_2974
  have hrat : ((452244123037 : ℚ) / 1000000000000) ≤ ((5653051521 : ℚ) / 12500000000) + (27143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244123037 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653051521 : ℚ) / 12500000000) : ℚ) : ℝ) + ((27143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27143:ℚ)^(-2:ℤ) : ℝ) = ((27143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2976 : ((((45224412439 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27143 < q → q < 27179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27179).mp (by decide +kernel))) hgap
  have hprev := s2L_2975
  have hrat : ((45224412439 : ℚ) / 100000000000) ≤ ((452244123037 : ℚ) / 1000000000000) + (27179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224412439 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452244123037 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27179:ℚ)^(-2:ℤ) : ℝ) = ((27179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2977 : ((((226122062871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27179 < q → q < 27191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27191).mp (by decide +kernel))) hgap
  have hprev := s2L_2976
  have hrat : ((226122062871 : ℚ) / 500000000000) ≤ ((45224412439 : ℚ) / 100000000000) + (27191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122062871 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224412439 : ℚ) / 100000000000) : ℚ) : ℝ) + ((27191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27191:ℚ)^(-2:ℤ) : ℝ) = ((27191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2978 : ((((452244127093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27191 < q → q < 27197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27197).mp (by decide +kernel))) hgap
  have hprev := s2L_2977
  have hrat : ((452244127093 : ℚ) / 1000000000000) ≤ ((226122062871 : ℚ) / 500000000000) + (27197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244127093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122062871 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27197:ℚ)^(-2:ℤ) : ℝ) = ((27197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2979 : ((((452244128443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27197 < q → q < 27211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27211).mp (by decide +kernel))) hgap
  have hprev := s2L_2978
  have hrat : ((452244128443 : ℚ) / 1000000000000) ≤ ((452244127093 : ℚ) / 1000000000000) + (27211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244128443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244127093 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27211:ℚ)^(-2:ℤ) : ℝ) = ((27211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2980 : ((((45224412979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27211 < q → q < 27239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27239).mp (by decide +kernel))) hgap
  have hprev := s2L_2979
  have hrat : ((45224412979 : ℚ) / 100000000000) ≤ ((452244128443 : ℚ) / 1000000000000) + (27239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224412979 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452244128443 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27239:ℚ)^(-2:ℤ) : ℝ) = ((27239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2981 : ((((452244131137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27239 < q → q < 27241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27241).mp (by decide +kernel))) hgap
  have hprev := s2L_2980
  have hrat : ((452244131137 : ℚ) / 1000000000000) ≤ ((45224412979 : ℚ) / 100000000000) + (27241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244131137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224412979 : ℚ) / 100000000000) : ℚ) : ℝ) + ((27241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27241:ℚ)^(-2:ℤ) : ℝ) = ((27241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2982 : ((((452244132483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27241 < q → q < 27253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27253).mp (by decide +kernel))) hgap
  have hprev := s2L_2981
  have hrat : ((452244132483 : ℚ) / 1000000000000) ≤ ((452244131137 : ℚ) / 1000000000000) + (27253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244132483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244131137 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27253:ℚ)^(-2:ℤ) : ℝ) = ((27253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2983 : ((((113061033457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27253 < q → q < 27259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27259).mp (by decide +kernel))) hgap
  have hprev := s2L_2982
  have hrat : ((113061033457 : ℚ) / 250000000000) ≤ ((452244132483 : ℚ) / 1000000000000) + (27259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061033457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244132483 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27259:ℚ)^(-2:ℤ) : ℝ) = ((27259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2984 : ((((113061033793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27259 < q → q < 27271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27271).mp (by decide +kernel))) hgap
  have hprev := s2L_2983
  have hrat : ((113061033793 : ℚ) / 250000000000) ≤ ((113061033457 : ℚ) / 250000000000) + (27271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061033793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113061033457 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27271:ℚ)^(-2:ℤ) : ℝ) = ((27271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2985 : ((((113061034129 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27271 < q → q < 27277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27277).mp (by decide +kernel))) hgap
  have hprev := s2L_2984
  have hrat : ((113061034129 : ℚ) / 250000000000) ≤ ((113061033793 : ℚ) / 250000000000) + (27277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061034129 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113061033793 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27277:ℚ)^(-2:ℤ) : ℝ) = ((27277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2986 : ((((452244137859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27277 < q → q < 27281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27281).mp (by decide +kernel))) hgap
  have hprev := s2L_2985
  have hrat : ((452244137859 : ℚ) / 1000000000000) ≤ ((113061034129 : ℚ) / 250000000000) + (27281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244137859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061034129 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27281:ℚ)^(-2:ℤ) : ℝ) = ((27281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2987 : ((((226122069601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27281 < q → q < 27283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27283).mp (by decide +kernel))) hgap
  have hprev := s2L_2986
  have hrat : ((226122069601 : ℚ) / 500000000000) ≤ ((452244137859 : ℚ) / 1000000000000) + (27283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122069601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244137859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27283:ℚ)^(-2:ℤ) : ℝ) = ((27283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2988 : ((((452244140543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27283 < q → q < 27299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27299).mp (by decide +kernel))) hgap
  have hprev := s2L_2987
  have hrat : ((452244140543 : ℚ) / 1000000000000) ≤ ((226122069601 : ℚ) / 500000000000) + (27299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244140543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122069601 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27299:ℚ)^(-2:ℤ) : ℝ) = ((27299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2989 : ((((452244141881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27299 < q → q < 27329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27329).mp (by decide +kernel))) hgap
  have hprev := s2L_2988
  have hrat : ((452244141881 : ℚ) / 1000000000000) ≤ ((452244140543 : ℚ) / 1000000000000) + (27329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244141881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244140543 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27329:ℚ)^(-2:ℤ) : ℝ) = ((27329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2990 : ((((452244143219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27329 < q → q < 27337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27337).mp (by decide +kernel))) hgap
  have hprev := s2L_2989
  have hrat : ((452244143219 : ℚ) / 1000000000000) ≤ ((452244141881 : ℚ) / 1000000000000) + (27337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244143219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244141881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27337:ℚ)^(-2:ℤ) : ℝ) = ((27337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2991 : ((((226122072277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27337 < q → q < 27361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27361).mp (by decide +kernel))) hgap
  have hprev := s2L_2990
  have hrat : ((226122072277 : ℚ) / 500000000000) ≤ ((452244143219 : ℚ) / 1000000000000) + (27361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122072277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244143219 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27361:ℚ)^(-2:ℤ) : ℝ) = ((27361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2992 : ((((452244145889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27361 < q → q < 27367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27367).mp (by decide +kernel))) hgap
  have hprev := s2L_2991
  have hrat : ((452244145889 : ℚ) / 1000000000000) ≤ ((226122072277 : ℚ) / 500000000000) + (27367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244145889 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122072277 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27367:ℚ)^(-2:ℤ) : ℝ) = ((27367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2993 : ((((452244147221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27367 < q → q < 27397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27397).mp (by decide +kernel))) hgap
  have hprev := s2L_2992
  have hrat : ((452244147221 : ℚ) / 1000000000000) ≤ ((452244145889 : ℚ) / 1000000000000) + (27397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244147221 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244145889 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27397:ℚ)^(-2:ℤ) : ℝ) = ((27397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2994 : ((((56530518569 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27397 < q → q < 27407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27407).mp (by decide +kernel))) hgap
  have hprev := s2L_2993
  have hrat : ((56530518569 : ℚ) / 125000000000) ≤ ((452244147221 : ℚ) / 1000000000000) + (27407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530518569 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244147221 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27407:ℚ)^(-2:ℤ) : ℝ) = ((27407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2995 : ((((452244149883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27407 < q → q < 27409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27409).mp (by decide +kernel))) hgap
  have hprev := s2L_2994
  have hrat : ((452244149883 : ℚ) / 1000000000000) ≤ ((56530518569 : ℚ) / 125000000000) + (27409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244149883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530518569 : ℚ) / 125000000000) : ℚ) : ℝ) + ((27409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27409:ℚ)^(-2:ℤ) : ℝ) = ((27409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2996 : ((((113061037803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27409 < q → q < 27427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27427).mp (by decide +kernel))) hgap
  have hprev := s2L_2995
  have hrat : ((113061037803 : ℚ) / 250000000000) ≤ ((452244149883 : ℚ) / 1000000000000) + (27427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061037803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244149883 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27427:ℚ)^(-2:ℤ) : ℝ) = ((27427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2997 : ((((22612207627 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27427 < q → q < 27431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27431).mp (by decide +kernel))) hgap
  have hprev := s2L_2996
  have hrat : ((22612207627 : ℚ) / 50000000000) ≤ ((113061037803 : ℚ) / 250000000000) + (27431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612207627 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113061037803 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27431:ℚ)^(-2:ℤ) : ℝ) = ((27431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2998 : ((((113061038467 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27431 < q → q < 27437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27437).mp (by decide +kernel))) hgap
  have hprev := s2L_2997
  have hrat : ((113061038467 : ℚ) / 250000000000) ≤ ((22612207627 : ℚ) / 50000000000) + (27437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061038467 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22612207627 : ℚ) / 50000000000) : ℚ) : ℝ) + ((27437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27437:ℚ)^(-2:ℤ) : ℝ) = ((27437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2999 : ((((90448831039 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27437 < q → q < 27449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27449).mp (by decide +kernel))) hgap
  have hprev := s2L_2998
  have hrat : ((90448831039 : ℚ) / 200000000000) ≤ ((113061038467 : ℚ) / 250000000000) + (27449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448831039 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113061038467 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27449:ℚ)^(-2:ℤ) : ℝ) = ((27449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3000 : ((((452244156521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27449 < q → q < 27457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27457).mp (by decide +kernel))) hgap
  have hprev := s2L_2999
  have hrat : ((452244156521 : ℚ) / 1000000000000) ≤ ((90448831039 : ℚ) / 200000000000) + (27457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244156521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448831039 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27457:ℚ)^(-2:ℤ) : ℝ) = ((27457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3001 : ((((90448831569 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27457 < q → q < 27479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27479).mp (by decide +kernel))) hgap
  have hprev := s2L_3000
  have hrat : ((90448831569 : ℚ) / 200000000000) ≤ ((452244156521 : ℚ) / 1000000000000) + (27479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448831569 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244156521 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27479:ℚ)^(-2:ℤ) : ℝ) = ((27479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3002 : ((((452244159169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27479 < q → q < 27481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27481).mp (by decide +kernel))) hgap
  have hprev := s2L_3001
  have hrat : ((452244159169 : ℚ) / 1000000000000) ≤ ((90448831569 : ℚ) / 200000000000) + (27481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244159169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448831569 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27481:ℚ)^(-2:ℤ) : ℝ) = ((27481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3003 : ((((113061040123 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27481 < q → q < 27487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27487).mp (by decide +kernel))) hgap
  have hprev := s2L_3002
  have hrat : ((113061040123 : ℚ) / 250000000000) ≤ ((452244159169 : ℚ) / 1000000000000) + (27487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061040123 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244159169 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27487:ℚ)^(-2:ℤ) : ℝ) = ((27487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3004 : ((((452244161813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27487 < q → q < 27509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27509).mp (by decide +kernel))) hgap
  have hprev := s2L_3003
  have hrat : ((452244161813 : ℚ) / 1000000000000) ≤ ((113061040123 : ℚ) / 250000000000) + (27509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244161813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061040123 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27509:ℚ)^(-2:ℤ) : ℝ) = ((27509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3005 : ((((113061040783 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27509 < q → q < 27527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27527).mp (by decide +kernel))) hgap
  have hprev := s2L_3004
  have hrat : ((113061040783 : ℚ) / 250000000000) ≤ ((452244161813 : ℚ) / 1000000000000) + (27527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061040783 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244161813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27527:ℚ)^(-2:ℤ) : ℝ) = ((27527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3006 : ((((452244164451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27527 < q → q < 27529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27529).mp (by decide +kernel))) hgap
  have hprev := s2L_3005
  have hrat : ((452244164451 : ℚ) / 1000000000000) ≤ ((113061040783 : ℚ) / 250000000000) + (27529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244164451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061040783 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27529:ℚ)^(-2:ℤ) : ℝ) = ((27529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3007 : ((((452244165769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27529 < q → q < 27539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27539).mp (by decide +kernel))) hgap
  have hprev := s2L_3006
  have hrat : ((452244165769 : ℚ) / 1000000000000) ≤ ((452244164451 : ℚ) / 1000000000000) + (27539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244165769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244164451 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27539:ℚ)^(-2:ℤ) : ℝ) = ((27539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3008 : ((((452244167087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27539 < q → q < 27541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27541).mp (by decide +kernel))) hgap
  have hprev := s2L_3007
  have hrat : ((452244167087 : ℚ) / 1000000000000) ≤ ((452244165769 : ℚ) / 1000000000000) + (27541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244167087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244165769 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27541:ℚ)^(-2:ℤ) : ℝ) = ((27541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3009 : ((((113061042101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27541 < q → q < 27551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27551).mp (by decide +kernel))) hgap
  have hprev := s2L_3008
  have hrat : ((113061042101 : ℚ) / 250000000000) ≤ ((452244167087 : ℚ) / 1000000000000) + (27551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061042101 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244167087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27551:ℚ)^(-2:ℤ) : ℝ) = ((27551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3010 : ((((226122084859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27551 < q → q < 27581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27581).mp (by decide +kernel))) hgap
  have hprev := s2L_3009
  have hrat : ((226122084859 : ℚ) / 500000000000) ≤ ((113061042101 : ℚ) / 250000000000) + (27581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122084859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061042101 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27581:ℚ)^(-2:ℤ) : ℝ) = ((27581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3011 : ((((56530521379 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27581 < q → q < 27583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27583).mp (by decide +kernel))) hgap
  have hprev := s2L_3010
  have hrat : ((56530521379 : ℚ) / 125000000000) ≤ ((226122084859 : ℚ) / 500000000000) + (27583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530521379 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122084859 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27583:ℚ)^(-2:ℤ) : ℝ) = ((27583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3012 : ((((452244172343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27583 < q → q < 27611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27611).mp (by decide +kernel))) hgap
  have hprev := s2L_3011
  have hrat : ((452244172343 : ℚ) / 1000000000000) ≤ ((56530521379 : ℚ) / 125000000000) + (27611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244172343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530521379 : ℚ) / 125000000000) : ℚ) : ℝ) + ((27611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27611:ℚ)^(-2:ℤ) : ℝ) = ((27611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3013 : ((((226122086827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27611 < q → q < 27617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27617).mp (by decide +kernel))) hgap
  have hprev := s2L_3012
  have hrat : ((226122086827 : ℚ) / 500000000000) ≤ ((452244172343 : ℚ) / 1000000000000) + (27617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122086827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244172343 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27617:ℚ)^(-2:ℤ) : ℝ) = ((27617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3014 : ((((452244174963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27617 < q → q < 27631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27631).mp (by decide +kernel))) hgap
  have hprev := s2L_3013
  have hrat : ((452244174963 : ℚ) / 1000000000000) ≤ ((226122086827 : ℚ) / 500000000000) + (27631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244174963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122086827 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27631:ℚ)^(-2:ℤ) : ℝ) = ((27631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3015 : ((((452244176271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27631 < q → q < 27647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27647).mp (by decide +kernel))) hgap
  have hprev := s2L_3014
  have hrat : ((452244176271 : ℚ) / 1000000000000) ≤ ((452244174963 : ℚ) / 1000000000000) + (27647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244176271 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244174963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27647:ℚ)^(-2:ℤ) : ℝ) = ((27647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3016 : ((((226122088789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27647 < q → q < 27653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27653).mp (by decide +kernel))) hgap
  have hprev := s2L_3015
  have hrat : ((226122088789 : ℚ) / 500000000000) ≤ ((452244176271 : ℚ) / 1000000000000) + (27653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122088789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244176271 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27653:ℚ)^(-2:ℤ) : ℝ) = ((27653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3017 : ((((452244178883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27653 < q → q < 27673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27673).mp (by decide +kernel))) hgap
  have hprev := s2L_3016
  have hrat : ((452244178883 : ℚ) / 1000000000000) ≤ ((226122088789 : ℚ) / 500000000000) + (27673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244178883 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122088789 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27673:ℚ)^(-2:ℤ) : ℝ) = ((27673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3018 : ((((452244180187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27673 < q → q < 27689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27689).mp (by decide +kernel))) hgap
  have hprev := s2L_3017
  have hrat : ((452244180187 : ℚ) / 1000000000000) ≤ ((452244178883 : ℚ) / 1000000000000) + (27689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244180187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244178883 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27689:ℚ)^(-2:ℤ) : ℝ) = ((27689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3019 : ((((452244181491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27689 < q → q < 27691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27691).mp (by decide +kernel))) hgap
  have hprev := s2L_3018
  have hrat : ((452244181491 : ℚ) / 1000000000000) ≤ ((452244180187 : ℚ) / 1000000000000) + (27691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244181491 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244180187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27691:ℚ)^(-2:ℤ) : ℝ) = ((27691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3020 : ((((226122091397 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27691 < q → q < 27697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27697).mp (by decide +kernel))) hgap
  have hprev := s2L_3019
  have hrat : ((226122091397 : ℚ) / 500000000000) ≤ ((452244181491 : ℚ) / 1000000000000) + (27697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122091397 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244181491 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27697:ℚ)^(-2:ℤ) : ℝ) = ((27697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3021 : ((((452244184097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27697 < q → q < 27701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27701).mp (by decide +kernel))) hgap
  have hprev := s2L_3020
  have hrat : ((452244184097 : ℚ) / 1000000000000) ≤ ((226122091397 : ℚ) / 500000000000) + (27701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244184097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122091397 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27701:ℚ)^(-2:ℤ) : ℝ) = ((27701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3022 : ((((452244185397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27701 < q → q < 27733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27733).mp (by decide +kernel))) hgap
  have hprev := s2L_3021
  have hrat : ((452244185397 : ℚ) / 1000000000000) ≤ ((452244184097 : ℚ) / 1000000000000) + (27733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244185397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244184097 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27733:ℚ)^(-2:ℤ) : ℝ) = ((27733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3023 : ((((56530523337 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27733 < q → q < 27737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27737).mp (by decide +kernel))) hgap
  have hprev := s2L_3022
  have hrat : ((56530523337 : ℚ) / 125000000000) ≤ ((452244185397 : ℚ) / 1000000000000) + (27737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530523337 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244185397 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27737:ℚ)^(-2:ℤ) : ℝ) = ((27737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3024 : ((((90448837599 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27737 < q → q < 27739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27739).mp (by decide +kernel))) hgap
  have hprev := s2L_3023
  have hrat : ((90448837599 : ℚ) / 200000000000) ≤ ((56530523337 : ℚ) / 125000000000) + (27739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448837599 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530523337 : ℚ) / 125000000000) : ℚ) : ℝ) + ((27739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27739:ℚ)^(-2:ℤ) : ℝ) = ((27739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3025 : ((((226122094647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27739 < q → q < 27743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27743).mp (by decide +kernel))) hgap
  have hprev := s2L_3024
  have hrat : ((226122094647 : ℚ) / 500000000000) ≤ ((90448837599 : ℚ) / 200000000000) + (27743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122094647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448837599 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27743:ℚ)^(-2:ℤ) : ℝ) = ((27743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3026 : ((((3533157739 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27743 < q → q < 27749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27749).mp (by decide +kernel))) hgap
  have hprev := s2L_3025
  have hrat : ((3533157739 : ℚ) / 7812500000) ≤ ((226122094647 : ℚ) / 500000000000) + (27749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533157739 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((226122094647 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27749:ℚ)^(-2:ℤ) : ℝ) = ((27749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3027 : ((((45224419189 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27749 < q → q < 27751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27751).mp (by decide +kernel))) hgap
  have hprev := s2L_3026
  have hrat : ((45224419189 : ℚ) / 100000000000) ≤ ((3533157739 : ℚ) / 7812500000) + (27751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224419189 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3533157739 : ℚ) / 7812500000) : ℚ) : ℝ) + ((27751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27751:ℚ)^(-2:ℤ) : ℝ) = ((27751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3028 : ((((452244193187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27751 < q → q < 27763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27763).mp (by decide +kernel))) hgap
  have hprev := s2L_3027
  have hrat : ((452244193187 : ℚ) / 1000000000000) ≤ ((45224419189 : ℚ) / 100000000000) + (27763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244193187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224419189 : ℚ) / 100000000000) : ℚ) : ℝ) + ((27763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27763:ℚ)^(-2:ℤ) : ℝ) = ((27763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3029 : ((((113061048621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27763 < q → q < 27767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27767).mp (by decide +kernel))) hgap
  have hprev := s2L_3028
  have hrat : ((113061048621 : ℚ) / 250000000000) ≤ ((452244193187 : ℚ) / 1000000000000) + (27767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061048621 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244193187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27767:ℚ)^(-2:ℤ) : ℝ) = ((27767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3030 : ((((22612209789 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27767 < q → q < 27773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27773).mp (by decide +kernel))) hgap
  have hprev := s2L_3029
  have hrat : ((22612209789 : ℚ) / 50000000000) ≤ ((113061048621 : ℚ) / 250000000000) + (27773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612209789 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113061048621 : ℚ) / 250000000000) : ℚ) : ℝ) + ((27773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27773:ℚ)^(-2:ℤ) : ℝ) = ((27773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3031 : ((((18089767883 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27773 < q → q < 27779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27779).mp (by decide +kernel))) hgap
  have hprev := s2L_3030
  have hrat : ((18089767883 : ℚ) / 40000000000) ≤ ((22612209789 : ℚ) / 50000000000) + (27779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089767883 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((22612209789 : ℚ) / 50000000000) : ℚ) : ℝ) + ((27779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27779:ℚ)^(-2:ℤ) : ℝ) = ((27779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3032 : ((((452244198369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27779 < q → q < 27791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27791).mp (by decide +kernel))) hgap
  have hprev := s2L_3031
  have hrat : ((452244198369 : ℚ) / 1000000000000) ≤ ((18089767883 : ℚ) / 40000000000) + (27791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244198369 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089767883 : ℚ) / 40000000000) : ℚ) : ℝ) + ((27791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27791:ℚ)^(-2:ℤ) : ℝ) = ((27791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3033 : ((((452244199663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27791 < q → q < 27793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27793).mp (by decide +kernel))) hgap
  have hprev := s2L_3032
  have hrat : ((452244199663 : ℚ) / 1000000000000) ≤ ((452244198369 : ℚ) / 1000000000000) + (27793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244199663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244198369 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27793:ℚ)^(-2:ℤ) : ℝ) = ((27793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3034 : ((((452244200957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27793 < q → q < 27799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27799).mp (by decide +kernel))) hgap
  have hprev := s2L_3033
  have hrat : ((452244200957 : ℚ) / 1000000000000) ≤ ((452244199663 : ℚ) / 1000000000000) + (27799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244200957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244199663 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27799:ℚ)^(-2:ℤ) : ℝ) = ((27799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3035 : ((((1808976809 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27799 < q → q < 27803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27803).mp (by decide +kernel))) hgap
  have hprev := s2L_3034
  have hrat : ((1808976809 : ℚ) / 4000000000) ≤ ((452244200957 : ℚ) / 1000000000000) + (27803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808976809 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((452244200957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27803:ℚ)^(-2:ℤ) : ℝ) = ((27803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3036 : ((((452244203543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27803 < q → q < 27809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27809).mp (by decide +kernel))) hgap
  have hprev := s2L_3035
  have hrat : ((452244203543 : ℚ) / 1000000000000) ≤ ((1808976809 : ℚ) / 4000000000) + (27809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244203543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1808976809 : ℚ) / 4000000000) : ℚ) : ℝ) + ((27809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27809:ℚ)^(-2:ℤ) : ℝ) = ((27809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3037 : ((((90448840967 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27809 < q → q < 27817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27817).mp (by decide +kernel))) hgap
  have hprev := s2L_3036
  have hrat : ((90448840967 : ℚ) / 200000000000) ≤ ((452244203543 : ℚ) / 1000000000000) + (27817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448840967 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244203543 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27817:ℚ)^(-2:ℤ) : ℝ) = ((27817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3038 : ((((226122103063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27817 < q → q < 27823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27823).mp (by decide +kernel))) hgap
  have hprev := s2L_3037
  have hrat : ((226122103063 : ℚ) / 500000000000) ≤ ((90448840967 : ℚ) / 200000000000) + (27823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122103063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448840967 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27823:ℚ)^(-2:ℤ) : ℝ) = ((27823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3039 : ((((452244207417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27823 < q → q < 27827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27827).mp (by decide +kernel))) hgap
  have hprev := s2L_3038
  have hrat : ((452244207417 : ℚ) / 1000000000000) ≤ ((226122103063 : ℚ) / 500000000000) + (27827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244207417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122103063 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27827:ℚ)^(-2:ℤ) : ℝ) = ((27827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3040 : ((((226122104353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27827 < q → q < 27847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27847).mp (by decide +kernel))) hgap
  have hprev := s2L_3039
  have hrat : ((226122104353 : ℚ) / 500000000000) ≤ ((452244207417 : ℚ) / 1000000000000) + (27847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122104353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244207417 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27847:ℚ)^(-2:ℤ) : ℝ) = ((27847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3041 : ((((90448841999 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27847 < q → q < 27851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27851).mp (by decide +kernel))) hgap
  have hprev := s2L_3040
  have hrat : ((90448841999 : ℚ) / 200000000000) ≤ ((226122104353 : ℚ) / 500000000000) + (27851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448841999 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226122104353 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27851:ℚ)^(-2:ℤ) : ℝ) = ((27851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3042 : ((((452244211281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27851 < q → q < 27883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27883).mp (by decide +kernel))) hgap
  have hprev := s2L_3041
  have hrat : ((452244211281 : ℚ) / 1000000000000) ≤ ((90448841999 : ℚ) / 200000000000) + (27883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244211281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448841999 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27883:ℚ)^(-2:ℤ) : ℝ) = ((27883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3043 : ((((226122106283 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27883 < q → q < 27893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27893).mp (by decide +kernel))) hgap
  have hprev := s2L_3042
  have hrat : ((226122106283 : ℚ) / 500000000000) ≤ ((452244211281 : ℚ) / 1000000000000) + (27893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122106283 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244211281 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27893:ℚ)^(-2:ℤ) : ℝ) = ((27893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3044 : ((((9044884277 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27893 < q → q < 27901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27901).mp (by decide +kernel))) hgap
  have hprev := s2L_3043
  have hrat : ((9044884277 : ℚ) / 20000000000) ≤ ((226122106283 : ℚ) / 500000000000) + (27901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044884277 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226122106283 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27901:ℚ)^(-2:ℤ) : ℝ) = ((27901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3045 : ((((452244215133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27901 < q → q < 27917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27917).mp (by decide +kernel))) hgap
  have hprev := s2L_3044
  have hrat : ((452244215133 : ℚ) / 1000000000000) ≤ ((9044884277 : ℚ) / 20000000000) + (27917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244215133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044884277 : ℚ) / 20000000000) : ℚ) : ℝ) + ((27917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27917:ℚ)^(-2:ℤ) : ℝ) = ((27917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3046 : ((((90448843283 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27917 < q → q < 27919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27919).mp (by decide +kernel))) hgap
  have hprev := s2L_3045
  have hrat : ((90448843283 : ℚ) / 200000000000) ≤ ((452244215133 : ℚ) / 1000000000000) + (27919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448843283 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244215133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27919:ℚ)^(-2:ℤ) : ℝ) = ((27919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3047 : ((((90448843539 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27919 < q → q < 27941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27941).mp (by decide +kernel))) hgap
  have hprev := s2L_3046
  have hrat : ((90448843539 : ℚ) / 200000000000) ≤ ((90448843283 : ℚ) / 200000000000) + (27941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448843539 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448843283 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27941:ℚ)^(-2:ℤ) : ℝ) = ((27941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3048 : ((((18089768759 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27941 < q → q < 27943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27943).mp (by decide +kernel))) hgap
  have hprev := s2L_3047
  have hrat : ((18089768759 : ℚ) / 40000000000) ≤ ((90448843539 : ℚ) / 200000000000) + (27943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089768759 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((90448843539 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27943:ℚ)^(-2:ℤ) : ℝ) = ((27943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3049 : ((((90448844051 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27943 < q → q < 27947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27947).mp (by decide +kernel))) hgap
  have hprev := s2L_3048
  have hrat : ((90448844051 : ℚ) / 200000000000) ≤ ((18089768759 : ℚ) / 40000000000) + (27947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448844051 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089768759 : ℚ) / 40000000000) : ℚ) : ℝ) + ((27947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27947:ℚ)^(-2:ℤ) : ℝ) = ((27947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3050 : ((((226122110767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27947 < q → q < 27953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27953).mp (by decide +kernel))) hgap
  have hprev := s2L_3049
  have hrat : ((226122110767 : ℚ) / 500000000000) ≤ ((90448844051 : ℚ) / 200000000000) + (27953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122110767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448844051 : ℚ) / 200000000000) : ℚ) : ℝ) + ((27953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27953:ℚ)^(-2:ℤ) : ℝ) = ((27953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3051 : ((((452244222813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27953 < q → q < 27961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27961).mp (by decide +kernel))) hgap
  have hprev := s2L_3050
  have hrat : ((452244222813 : ℚ) / 1000000000000) ≤ ((226122110767 : ℚ) / 500000000000) + (27961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244222813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122110767 : ℚ) / 500000000000) : ℚ) : ℝ) + ((27961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27961:ℚ)^(-2:ℤ) : ℝ) = ((27961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3052 : ((((452244224091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27961 < q → q < 27967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27967).mp (by decide +kernel))) hgap
  have hprev := s2L_3051
  have hrat : ((452244224091 : ℚ) / 1000000000000) ≤ ((452244222813 : ℚ) / 1000000000000) + (27967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244224091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244222813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27967:ℚ)^(-2:ℤ) : ℝ) = ((27967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3053 : ((((56530528171 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27967 < q → q < 27983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27983).mp (by decide +kernel))) hgap
  have hprev := s2L_3052
  have hrat : ((56530528171 : ℚ) / 125000000000) ≤ ((452244224091 : ℚ) / 1000000000000) + (27983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530528171 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244224091 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((27983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27983:ℚ)^(-2:ℤ) : ℝ) = ((27983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3054 : ((((452244226643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 27997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27983 < q → q < 27997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 27997).mp (by decide +kernel))) hgap
  have hprev := s2L_3053
  have hrat : ((452244226643 : ℚ) / 1000000000000) ≤ ((56530528171 : ℚ) / 125000000000) + (27997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244226643 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530528171 : ℚ) / 125000000000) : ℚ) : ℝ) + ((27997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((27997:ℚ)^(-2:ℤ) : ℝ) = ((27997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3055 : ((((226122113959 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 27997 < q → q < 28001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28001).mp (by decide +kernel))) hgap
  have hprev := s2L_3054
  have hrat : ((226122113959 : ℚ) / 500000000000) ≤ ((452244226643 : ℚ) / 1000000000000) + (28001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122113959 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244226643 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28001:ℚ)^(-2:ℤ) : ℝ) = ((28001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3056 : ((((452244229191 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28001 < q → q < 28019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28019).mp (by decide +kernel))) hgap
  have hprev := s2L_3055
  have hrat : ((452244229191 : ℚ) / 1000000000000) ≤ ((226122113959 : ℚ) / 500000000000) + (28019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244229191 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122113959 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28019:ℚ)^(-2:ℤ) : ℝ) = ((28019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3057 : ((((7066316101 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28019 < q → q < 28027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28027).mp (by decide +kernel))) hgap
  have hprev := s2L_3056
  have hrat : ((7066316101 : ℚ) / 15625000000) ≤ ((452244229191 : ℚ) / 1000000000000) + (28027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066316101 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452244229191 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28027:ℚ)^(-2:ℤ) : ℝ) = ((28027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3058 : ((((56530528967 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28027 < q → q < 28031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28031).mp (by decide +kernel))) hgap
  have hprev := s2L_3057
  have hrat : ((56530528967 : ℚ) / 125000000000) ≤ ((7066316101 : ℚ) / 15625000000) + (28031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530528967 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((7066316101 : ℚ) / 15625000000) : ℚ) : ℝ) + ((28031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28031:ℚ)^(-2:ℤ) : ℝ) = ((28031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3059 : ((((226122116503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28031 < q → q < 28051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28051).mp (by decide +kernel))) hgap
  have hprev := s2L_3058
  have hrat : ((226122116503 : ℚ) / 500000000000) ≤ ((56530528967 : ℚ) / 125000000000) + (28051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122116503 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530528967 : ℚ) / 125000000000) : ℚ) : ℝ) + ((28051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28051:ℚ)^(-2:ℤ) : ℝ) = ((28051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3060 : ((((113061058569 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28051 < q → q < 28057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28057).mp (by decide +kernel))) hgap
  have hprev := s2L_3059
  have hrat : ((113061058569 : ℚ) / 250000000000) ≤ ((226122116503 : ℚ) / 500000000000) + (28057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061058569 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122116503 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28057:ℚ)^(-2:ℤ) : ℝ) = ((28057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3061 : ((((90448847109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28057 < q → q < 28069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28069).mp (by decide +kernel))) hgap
  have hprev := s2L_3060
  have hrat : ((90448847109 : ℚ) / 200000000000) ≤ ((113061058569 : ℚ) / 250000000000) + (28069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448847109 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113061058569 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28069:ℚ)^(-2:ℤ) : ℝ) = ((28069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3062 : ((((452244236813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28069 < q → q < 28081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28081).mp (by decide +kernel))) hgap
  have hprev := s2L_3061
  have hrat : ((452244236813 : ℚ) / 1000000000000) ≤ ((90448847109 : ℚ) / 200000000000) + (28081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244236813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448847109 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28081:ℚ)^(-2:ℤ) : ℝ) = ((28081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3063 : ((((353315811 : ℚ) / 781250000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28081 < q → q < 28087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28087).mp (by decide +kernel))) hgap
  have hprev := s2L_3062
  have hrat : ((353315811 : ℚ) / 781250000) ≤ ((452244236813 : ℚ) / 1000000000000) + (28087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((353315811 : ℚ) / 781250000) : ℚ) : ℝ) ≤ ((((452244236813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28087:ℚ)^(-2:ℤ) : ℝ) = ((28087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3064 : ((((226122119673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28087 < q → q < 28097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28097).mp (by decide +kernel))) hgap
  have hprev := s2L_3063
  have hrat : ((226122119673 : ℚ) / 500000000000) ≤ ((353315811 : ℚ) / 781250000) + (28097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122119673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((353315811 : ℚ) / 781250000) : ℚ) : ℝ) + ((28097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28097:ℚ)^(-2:ℤ) : ℝ) = ((28097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3065 : ((((113061060153 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28097 < q → q < 28099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28099).mp (by decide +kernel))) hgap
  have hprev := s2L_3064
  have hrat : ((113061060153 : ℚ) / 250000000000) ≤ ((226122119673 : ℚ) / 500000000000) + (28099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061060153 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122119673 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28099:ℚ)^(-2:ℤ) : ℝ) = ((28099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3066 : ((((452244241877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28099 < q → q < 28109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28109).mp (by decide +kernel))) hgap
  have hprev := s2L_3065
  have hrat : ((452244241877 : ℚ) / 1000000000000) ≤ ((113061060153 : ℚ) / 250000000000) + (28109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244241877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061060153 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28109:ℚ)^(-2:ℤ) : ℝ) = ((28109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3067 : ((((226122121571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28109 < q → q < 28111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28111).mp (by decide +kernel))) hgap
  have hprev := s2L_3066
  have hrat : ((226122121571 : ℚ) / 500000000000) ≤ ((452244241877 : ℚ) / 1000000000000) + (28111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122121571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244241877 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28111:ℚ)^(-2:ℤ) : ℝ) = ((28111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3068 : ((((226122122203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28111 < q → q < 28123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28123).mp (by decide +kernel))) hgap
  have hprev := s2L_3067
  have hrat : ((226122122203 : ℚ) / 500000000000) ≤ ((226122121571 : ℚ) / 500000000000) + (28123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122122203 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122121571 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28123:ℚ)^(-2:ℤ) : ℝ) = ((28123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3069 : ((((452244245667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28123 < q → q < 28151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28151).mp (by decide +kernel))) hgap
  have hprev := s2L_3068
  have hrat : ((452244245667 : ℚ) / 1000000000000) ≤ ((226122122203 : ℚ) / 500000000000) + (28151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244245667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122122203 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28151:ℚ)^(-2:ℤ) : ℝ) = ((28151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3070 : ((((452244246927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28151 < q → q < 28163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28163).mp (by decide +kernel))) hgap
  have hprev := s2L_3069
  have hrat : ((452244246927 : ℚ) / 1000000000000) ≤ ((452244245667 : ℚ) / 1000000000000) + (28163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244246927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244245667 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28163:ℚ)^(-2:ℤ) : ℝ) = ((28163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3071 : ((((226122124093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28163 < q → q < 28181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28181).mp (by decide +kernel))) hgap
  have hprev := s2L_3070
  have hrat : ((226122124093 : ℚ) / 500000000000) ≤ ((452244246927 : ℚ) / 1000000000000) + (28181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122124093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244246927 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28181:ℚ)^(-2:ℤ) : ℝ) = ((28181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3072 : ((((113061062361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28181 < q → q < 28183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28183).mp (by decide +kernel))) hgap
  have hprev := s2L_3071
  have hrat : ((113061062361 : ℚ) / 250000000000) ≤ ((226122124093 : ℚ) / 500000000000) + (28183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061062361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122124093 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28183:ℚ)^(-2:ℤ) : ℝ) = ((28183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3073 : ((((452244250701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28183 < q → q < 28201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28201).mp (by decide +kernel))) hgap
  have hprev := s2L_3072
  have hrat : ((452244250701 : ℚ) / 1000000000000) ≤ ((113061062361 : ℚ) / 250000000000) + (28201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244250701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061062361 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28201:ℚ)^(-2:ℤ) : ℝ) = ((28201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3074 : ((((452244251957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28201 < q → q < 28211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28211).mp (by decide +kernel))) hgap
  have hprev := s2L_3073
  have hrat : ((452244251957 : ℚ) / 1000000000000) ≤ ((452244250701 : ℚ) / 1000000000000) + (28211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244251957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244250701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28211:ℚ)^(-2:ℤ) : ℝ) = ((28211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3075 : ((((113061063303 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28211 < q → q < 28219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28219).mp (by decide +kernel))) hgap
  have hprev := s2L_3074
  have hrat : ((113061063303 : ℚ) / 250000000000) ≤ ((452244251957 : ℚ) / 1000000000000) + (28219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061063303 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244251957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28219:ℚ)^(-2:ℤ) : ℝ) = ((28219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3076 : ((((226122127233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28219 < q → q < 28229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28229).mp (by decide +kernel))) hgap
  have hprev := s2L_3075
  have hrat : ((226122127233 : ℚ) / 500000000000) ≤ ((113061063303 : ℚ) / 250000000000) + (28229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122127233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061063303 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28229:ℚ)^(-2:ℤ) : ℝ) = ((28229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3077 : ((((113061063929 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28229 < q → q < 28277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28277).mp (by decide +kernel))) hgap
  have hprev := s2L_3076
  have hrat : ((113061063929 : ℚ) / 250000000000) ≤ ((226122127233 : ℚ) / 500000000000) + (28277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061063929 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122127233 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28277:ℚ)^(-2:ℤ) : ℝ) = ((28277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3078 : ((((226122128483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28277 < q → q < 28279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28279).mp (by decide +kernel))) hgap
  have hprev := s2L_3077
  have hrat : ((226122128483 : ℚ) / 500000000000) ≤ ((113061063929 : ℚ) / 250000000000) + (28279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122128483 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061063929 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28279:ℚ)^(-2:ℤ) : ℝ) = ((28279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3079 : ((((56530532277 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28279 < q → q < 28283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28283).mp (by decide +kernel))) hgap
  have hprev := s2L_3078
  have hrat : ((56530532277 : ℚ) / 125000000000) ≤ ((226122128483 : ℚ) / 500000000000) + (28283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530532277 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226122128483 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28283:ℚ)^(-2:ℤ) : ℝ) = ((28283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3080 : ((((90448851893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28283 < q → q < 28289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28289).mp (by decide +kernel))) hgap
  have hprev := s2L_3079
  have hrat : ((90448851893 : ℚ) / 200000000000) ≤ ((56530532277 : ℚ) / 125000000000) + (28289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448851893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530532277 : ℚ) / 125000000000) : ℚ) : ℝ) + ((28289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28289:ℚ)^(-2:ℤ) : ℝ) = ((28289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3081 : ((((452244260713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28289 < q → q < 28297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28297).mp (by decide +kernel))) hgap
  have hprev := s2L_3080
  have hrat : ((452244260713 : ℚ) / 1000000000000) ≤ ((90448851893 : ℚ) / 200000000000) + (28297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244260713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448851893 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28297:ℚ)^(-2:ℤ) : ℝ) = ((28297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3082 : ((((11306106549 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28297 < q → q < 28307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28307).mp (by decide +kernel))) hgap
  have hprev := s2L_3081
  have hrat : ((11306106549 : ℚ) / 25000000000) ≤ ((452244260713 : ℚ) / 1000000000000) + (28307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306106549 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452244260713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28307:ℚ)^(-2:ℤ) : ℝ) = ((28307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3083 : ((((452244263207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28307 < q → q < 28309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28309).mp (by decide +kernel))) hgap
  have hprev := s2L_3082
  have hrat : ((452244263207 : ℚ) / 1000000000000) ≤ ((11306106549 : ℚ) / 25000000000) + (28309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244263207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306106549 : ℚ) / 25000000000) : ℚ) : ℝ) + ((28309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28309:ℚ)^(-2:ℤ) : ℝ) = ((28309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3084 : ((((452244264453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28309 < q → q < 28319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28319).mp (by decide +kernel))) hgap
  have hprev := s2L_3083
  have hrat : ((452244264453 : ℚ) / 1000000000000) ≤ ((452244263207 : ℚ) / 1000000000000) + (28319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244264453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244263207 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28319:ℚ)^(-2:ℤ) : ℝ) = ((28319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3085 : ((((452244265697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28319 < q → q < 28349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28349).mp (by decide +kernel))) hgap
  have hprev := s2L_3084
  have hrat : ((452244265697 : ℚ) / 1000000000000) ≤ ((452244264453 : ℚ) / 1000000000000) + (28349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244265697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244264453 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28349:ℚ)^(-2:ℤ) : ℝ) = ((28349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3086 : ((((452244266941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28349 < q → q < 28351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28351).mp (by decide +kernel))) hgap
  have hprev := s2L_3085
  have hrat : ((452244266941 : ℚ) / 1000000000000) ≤ ((452244265697 : ℚ) / 1000000000000) + (28351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244266941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244265697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28351:ℚ)^(-2:ℤ) : ℝ) = ((28351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3087 : ((((452244268181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28351 < q → q < 28387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28387).mp (by decide +kernel))) hgap
  have hprev := s2L_3086
  have hrat : ((452244268181 : ℚ) / 1000000000000) ≤ ((452244266941 : ℚ) / 1000000000000) + (28387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244268181 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244266941 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28387:ℚ)^(-2:ℤ) : ℝ) = ((28387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3088 : ((((452244269421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28387 < q → q < 28393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28393).mp (by decide +kernel))) hgap
  have hprev := s2L_3087
  have hrat : ((452244269421 : ℚ) / 1000000000000) ≤ ((452244268181 : ℚ) / 1000000000000) + (28393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244269421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244268181 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28393:ℚ)^(-2:ℤ) : ℝ) = ((28393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3089 : ((((22612213533 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28403, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28393 < q → q < 28403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28403).mp (by decide +kernel))) hgap
  have hprev := s2L_3088
  have hrat : ((22612213533 : ℚ) / 50000000000) ≤ ((452244269421 : ℚ) / 1000000000000) + (28403:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612213533 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452244269421 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28403:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28403:ℚ)^(-2:ℤ) : ℝ) = ((28403:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3090 : ((((452244271899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28403 < q → q < 28409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28409).mp (by decide +kernel))) hgap
  have hprev := s2L_3089
  have hrat : ((452244271899 : ℚ) / 1000000000000) ≤ ((22612213533 : ℚ) / 50000000000) + (28409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244271899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612213533 : ℚ) / 50000000000) : ℚ) : ℝ) + ((28409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28409:ℚ)^(-2:ℤ) : ℝ) = ((28409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3091 : ((((452244273137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28409 < q → q < 28411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28411).mp (by decide +kernel))) hgap
  have hprev := s2L_3090
  have hrat : ((452244273137 : ℚ) / 1000000000000) ≤ ((452244271899 : ℚ) / 1000000000000) + (28411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244273137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244271899 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28411:ℚ)^(-2:ℤ) : ℝ) = ((28411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3092 : ((((226122137187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28411 < q → q < 28429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28429).mp (by decide +kernel))) hgap
  have hprev := s2L_3091
  have hrat : ((226122137187 : ℚ) / 500000000000) ≤ ((452244273137 : ℚ) / 1000000000000) + (28429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122137187 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244273137 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28429:ℚ)^(-2:ℤ) : ℝ) = ((28429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3093 : ((((45224427561 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28429 < q → q < 28433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28433).mp (by decide +kernel))) hgap
  have hprev := s2L_3092
  have hrat : ((45224427561 : ℚ) / 100000000000) ≤ ((226122137187 : ℚ) / 500000000000) + (28433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224427561 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226122137187 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28433:ℚ)^(-2:ℤ) : ℝ) = ((28433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3094 : ((((226122138423 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28433 < q → q < 28439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28439).mp (by decide +kernel))) hgap
  have hprev := s2L_3093
  have hrat : ((226122138423 : ℚ) / 500000000000) ≤ ((45224427561 : ℚ) / 100000000000) + (28439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122138423 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224427561 : ℚ) / 100000000000) : ℚ) : ℝ) + ((28439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28439:ℚ)^(-2:ℤ) : ℝ) = ((28439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3095 : ((((452244278081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28439 < q → q < 28447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28447).mp (by decide +kernel))) hgap
  have hprev := s2L_3094
  have hrat : ((452244278081 : ℚ) / 1000000000000) ≤ ((226122138423 : ℚ) / 500000000000) + (28447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244278081 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122138423 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28447:ℚ)^(-2:ℤ) : ℝ) = ((28447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3096 : ((((90448855863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28447 < q → q < 28463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28463).mp (by decide +kernel))) hgap
  have hprev := s2L_3095
  have hrat : ((90448855863 : ℚ) / 200000000000) ≤ ((452244278081 : ℚ) / 1000000000000) + (28463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448855863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244278081 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28463:ℚ)^(-2:ℤ) : ℝ) = ((28463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3097 : ((((113061070137 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28463 < q → q < 28477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28477).mp (by decide +kernel))) hgap
  have hprev := s2L_3096
  have hrat : ((113061070137 : ℚ) / 250000000000) ≤ ((90448855863 : ℚ) / 200000000000) + (28477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061070137 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448855863 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28477:ℚ)^(-2:ℤ) : ℝ) = ((28477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3098 : ((((452244281779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28477 < q → q < 28493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28493).mp (by decide +kernel))) hgap
  have hprev := s2L_3097
  have hrat : ((452244281779 : ℚ) / 1000000000000) ≤ ((113061070137 : ℚ) / 250000000000) + (28493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244281779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061070137 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28493:ℚ)^(-2:ℤ) : ℝ) = ((28493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3099 : ((((45224428301 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28493 < q → q < 28499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28499).mp (by decide +kernel))) hgap
  have hprev := s2L_3098
  have hrat : ((45224428301 : ℚ) / 100000000000) ≤ ((452244281779 : ℚ) / 1000000000000) + (28499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224428301 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452244281779 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28499:ℚ)^(-2:ℤ) : ℝ) = ((28499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3100 : ((((5653053553 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28499 < q → q < 28513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28513).mp (by decide +kernel))) hgap
  have hprev := s2L_3099
  have hrat : ((5653053553 : ℚ) / 12500000000) ≤ ((45224428301 : ℚ) / 100000000000) + (28513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653053553 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((45224428301 : ℚ) / 100000000000) : ℚ) : ℝ) + ((28513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28513:ℚ)^(-2:ℤ) : ℝ) = ((28513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3101 : ((((452244285469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28513 < q → q < 28517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28517).mp (by decide +kernel))) hgap
  have hprev := s2L_3100
  have hrat : ((452244285469 : ℚ) / 1000000000000) ≤ ((5653053553 : ℚ) / 12500000000) + (28517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244285469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653053553 : ℚ) / 12500000000) : ℚ) : ℝ) + ((28517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28517:ℚ)^(-2:ℤ) : ℝ) = ((28517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3102 : ((((56530535837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28517 < q → q < 28537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28537).mp (by decide +kernel))) hgap
  have hprev := s2L_3101
  have hrat : ((56530535837 : ℚ) / 125000000000) ≤ ((452244285469 : ℚ) / 1000000000000) + (28537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530535837 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244285469 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28537:ℚ)^(-2:ℤ) : ℝ) = ((28537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3103 : ((((452244287923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28537 < q → q < 28541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28541).mp (by decide +kernel))) hgap
  have hprev := s2L_3102
  have hrat : ((452244287923 : ℚ) / 1000000000000) ≤ ((56530535837 : ℚ) / 125000000000) + (28541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244287923 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530535837 : ℚ) / 125000000000) : ℚ) : ℝ) + ((28541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28541:ℚ)^(-2:ℤ) : ℝ) = ((28541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3104 : ((((9044885783 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28541 < q → q < 28547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28547).mp (by decide +kernel))) hgap
  have hprev := s2L_3103
  have hrat : ((9044885783 : ℚ) / 20000000000) ≤ ((452244287923 : ℚ) / 1000000000000) + (28547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044885783 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452244287923 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28547:ℚ)^(-2:ℤ) : ℝ) = ((28547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3105 : ((((56530536297 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28547 < q → q < 28549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28549).mp (by decide +kernel))) hgap
  have hprev := s2L_3104
  have hrat : ((56530536297 : ℚ) / 125000000000) ≤ ((9044885783 : ℚ) / 20000000000) + (28549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530536297 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((9044885783 : ℚ) / 20000000000) : ℚ) : ℝ) + ((28549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28549:ℚ)^(-2:ℤ) : ℝ) = ((28549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3106 : ((((226122145801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28549 < q → q < 28559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28559).mp (by decide +kernel))) hgap
  have hprev := s2L_3105
  have hrat : ((226122145801 : ℚ) / 500000000000) ≤ ((56530536297 : ℚ) / 125000000000) + (28559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122145801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530536297 : ℚ) / 125000000000) : ℚ) : ℝ) + ((28559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28559:ℚ)^(-2:ℤ) : ℝ) = ((28559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3107 : ((((452244292827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28559 < q → q < 28571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28571).mp (by decide +kernel))) hgap
  have hprev := s2L_3106
  have hrat : ((452244292827 : ℚ) / 1000000000000) ≤ ((226122145801 : ℚ) / 500000000000) + (28571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244292827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122145801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28571:ℚ)^(-2:ℤ) : ℝ) = ((28571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3108 : ((((452244294051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28571 < q → q < 28573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28573).mp (by decide +kernel))) hgap
  have hprev := s2L_3107
  have hrat : ((452244294051 : ℚ) / 1000000000000) ≤ ((452244292827 : ℚ) / 1000000000000) + (28573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244294051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244292827 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28573:ℚ)^(-2:ℤ) : ℝ) = ((28573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3109 : ((((18089771811 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28573 < q → q < 28579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28579).mp (by decide +kernel))) hgap
  have hprev := s2L_3108
  have hrat : ((18089771811 : ℚ) / 40000000000) ≤ ((452244294051 : ℚ) / 1000000000000) + (28579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089771811 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244294051 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28579:ℚ)^(-2:ℤ) : ℝ) = ((28579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3110 : ((((226122148249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28579 < q → q < 28591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28591).mp (by decide +kernel))) hgap
  have hprev := s2L_3109
  have hrat : ((226122148249 : ℚ) / 500000000000) ≤ ((18089771811 : ℚ) / 40000000000) + (28591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122148249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089771811 : ℚ) / 40000000000) : ℚ) : ℝ) + ((28591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28591:ℚ)^(-2:ℤ) : ℝ) = ((28591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3111 : ((((11306107443 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28591 < q → q < 28597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28597).mp (by decide +kernel))) hgap
  have hprev := s2L_3110
  have hrat : ((11306107443 : ℚ) / 25000000000) ≤ ((226122148249 : ℚ) / 500000000000) + (28597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306107443 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226122148249 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28597:ℚ)^(-2:ℤ) : ℝ) = ((28597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3112 : ((((226122149471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28597 < q → q < 28603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28603).mp (by decide +kernel))) hgap
  have hprev := s2L_3111
  have hrat : ((226122149471 : ℚ) / 500000000000) ≤ ((11306107443 : ℚ) / 25000000000) + (28603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122149471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11306107443 : ℚ) / 25000000000) : ℚ) : ℝ) + ((28603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28603:ℚ)^(-2:ℤ) : ℝ) = ((28603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3113 : ((((452244300163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28603 < q → q < 28607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28607).mp (by decide +kernel))) hgap
  have hprev := s2L_3112
  have hrat : ((452244300163 : ℚ) / 1000000000000) ≤ ((226122149471 : ℚ) / 500000000000) + (28607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244300163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122149471 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28607:ℚ)^(-2:ℤ) : ℝ) = ((28607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3114 : ((((452244301383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28607 < q → q < 28619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28619).mp (by decide +kernel))) hgap
  have hprev := s2L_3113
  have hrat : ((452244301383 : ℚ) / 1000000000000) ≤ ((452244300163 : ℚ) / 1000000000000) + (28619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244301383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244300163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28619:ℚ)^(-2:ℤ) : ℝ) = ((28619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3115 : ((((452244302603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28619 < q → q < 28621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28621).mp (by decide +kernel))) hgap
  have hprev := s2L_3114
  have hrat : ((452244302603 : ℚ) / 1000000000000) ≤ ((452244301383 : ℚ) / 1000000000000) + (28621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244302603 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244301383 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28621:ℚ)^(-2:ℤ) : ℝ) = ((28621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3116 : ((((452244303823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28621 < q → q < 28627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28627).mp (by decide +kernel))) hgap
  have hprev := s2L_3115
  have hrat : ((452244303823 : ℚ) / 1000000000000) ≤ ((452244302603 : ℚ) / 1000000000000) + (28627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244303823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244302603 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28627:ℚ)^(-2:ℤ) : ℝ) = ((28627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3117 : ((((226122152521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28627 < q → q < 28631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28631).mp (by decide +kernel))) hgap
  have hprev := s2L_3116
  have hrat : ((226122152521 : ℚ) / 500000000000) ≤ ((452244303823 : ℚ) / 1000000000000) + (28631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122152521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244303823 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28631:ℚ)^(-2:ℤ) : ℝ) = ((28631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3118 : ((((22612215313 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28631 < q → q < 28643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28643).mp (by decide +kernel))) hgap
  have hprev := s2L_3117
  have hrat : ((22612215313 : ℚ) / 50000000000) ≤ ((226122152521 : ℚ) / 500000000000) + (28643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612215313 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226122152521 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28643:ℚ)^(-2:ℤ) : ℝ) = ((28643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3119 : ((((226122153739 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28643 < q → q < 28649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28649).mp (by decide +kernel))) hgap
  have hprev := s2L_3118
  have hrat : ((226122153739 : ℚ) / 500000000000) ≤ ((22612215313 : ℚ) / 50000000000) + (28649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122153739 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612215313 : ℚ) / 50000000000) : ℚ) : ℝ) + ((28649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28649:ℚ)^(-2:ℤ) : ℝ) = ((28649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3120 : ((((90448861739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28649 < q → q < 28657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28657).mp (by decide +kernel))) hgap
  have hprev := s2L_3119
  have hrat : ((90448861739 : ℚ) / 200000000000) ≤ ((226122153739 : ℚ) / 500000000000) + (28657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448861739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226122153739 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28657:ℚ)^(-2:ℤ) : ℝ) = ((28657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3121 : ((((56530538739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28657 < q → q < 28661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28661).mp (by decide +kernel))) hgap
  have hprev := s2L_3120
  have hrat : ((56530538739 : ℚ) / 125000000000) ≤ ((90448861739 : ℚ) / 200000000000) + (28661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530538739 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90448861739 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28661:ℚ)^(-2:ℤ) : ℝ) = ((28661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3122 : ((((452244311129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28661 < q → q < 28663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28663).mp (by decide +kernel))) hgap
  have hprev := s2L_3121
  have hrat : ((452244311129 : ℚ) / 1000000000000) ≤ ((56530538739 : ℚ) / 125000000000) + (28663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244311129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530538739 : ℚ) / 125000000000) : ℚ) : ℝ) + ((28663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28663:ℚ)^(-2:ℤ) : ℝ) = ((28663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3123 : ((((90448862469 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28663 < q → q < 28669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28669).mp (by decide +kernel))) hgap
  have hprev := s2L_3122
  have hrat : ((90448862469 : ℚ) / 200000000000) ≤ ((452244311129 : ℚ) / 1000000000000) + (28669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448862469 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244311129 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28669:ℚ)^(-2:ℤ) : ℝ) = ((28669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3124 : ((((11306107839 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28669 < q → q < 28687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28687).mp (by decide +kernel))) hgap
  have hprev := s2L_3123
  have hrat : ((11306107839 : ℚ) / 25000000000) ≤ ((90448862469 : ℚ) / 200000000000) + (28687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306107839 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((90448862469 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28687:ℚ)^(-2:ℤ) : ℝ) = ((28687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3125 : ((((226122157387 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28687 < q → q < 28697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28697).mp (by decide +kernel))) hgap
  have hprev := s2L_3124
  have hrat : ((226122157387 : ℚ) / 500000000000) ≤ ((11306107839 : ℚ) / 25000000000) + (28697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122157387 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11306107839 : ℚ) / 25000000000) : ℚ) : ℝ) + ((28697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28697:ℚ)^(-2:ℤ) : ℝ) = ((28697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3126 : ((((452244315987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28697 < q → q < 28703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28703).mp (by decide +kernel))) hgap
  have hprev := s2L_3125
  have hrat : ((452244315987 : ℚ) / 1000000000000) ≤ ((226122157387 : ℚ) / 500000000000) + (28703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244315987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122157387 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28703:ℚ)^(-2:ℤ) : ℝ) = ((28703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3127 : ((((1130610793 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28703 < q → q < 28711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28711).mp (by decide +kernel))) hgap
  have hprev := s2L_3126
  have hrat : ((1130610793 : ℚ) / 2500000000) ≤ ((452244315987 : ℚ) / 1000000000000) + (28711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1130610793 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((452244315987 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28711:ℚ)^(-2:ℤ) : ℝ) = ((28711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3128 : ((((113061079603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28711 < q → q < 28723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28723).mp (by decide +kernel))) hgap
  have hprev := s2L_3127
  have hrat : ((113061079603 : ℚ) / 250000000000) ≤ ((1130610793 : ℚ) / 2500000000) + (28723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061079603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((1130610793 : ℚ) / 2500000000) : ℚ) : ℝ) + ((28723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28723:ℚ)^(-2:ℤ) : ℝ) = ((28723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3129 : ((((452244319623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28723 < q → q < 28729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28729).mp (by decide +kernel))) hgap
  have hprev := s2L_3128
  have hrat : ((452244319623 : ℚ) / 1000000000000) ≤ ((113061079603 : ℚ) / 250000000000) + (28729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244319623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061079603 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28729:ℚ)^(-2:ℤ) : ℝ) = ((28729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3130 : ((((7066317513 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28729 < q → q < 28751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28751).mp (by decide +kernel))) hgap
  have hprev := s2L_3129
  have hrat : ((7066317513 : ℚ) / 15625000000) ≤ ((452244319623 : ℚ) / 1000000000000) + (28751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066317513 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452244319623 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28751:ℚ)^(-2:ℤ) : ℝ) = ((28751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3131 : ((((452244322041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28751 < q → q < 28753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28753).mp (by decide +kernel))) hgap
  have hprev := s2L_3130
  have hrat : ((452244322041 : ℚ) / 1000000000000) ≤ ((7066317513 : ℚ) / 15625000000) + (28753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244322041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066317513 : ℚ) / 15625000000) : ℚ) : ℝ) + ((28753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28753:ℚ)^(-2:ℤ) : ℝ) = ((28753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3132 : ((((1808977293 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28753 < q → q < 28759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28759).mp (by decide +kernel))) hgap
  have hprev := s2L_3131
  have hrat : ((1808977293 : ℚ) / 4000000000) ≤ ((452244322041 : ℚ) / 1000000000000) + (28759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808977293 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((452244322041 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28759:ℚ)^(-2:ℤ) : ℝ) = ((28759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3133 : ((((226122162229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28771, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28759 < q → q < 28771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28771).mp (by decide +kernel))) hgap
  have hprev := s2L_3132
  have hrat : ((226122162229 : ℚ) / 500000000000) ≤ ((1808977293 : ℚ) / 4000000000) + (28771:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122162229 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1808977293 : ℚ) / 4000000000) : ℚ) : ℝ) + ((28771:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28771:ℚ)^(-2:ℤ) : ℝ) = ((28771:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3134 : ((((14132635177 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28771 < q → q < 28789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28789).mp (by decide +kernel))) hgap
  have hprev := s2L_3133
  have hrat : ((14132635177 : ℚ) / 31250000000) ≤ ((226122162229 : ℚ) / 500000000000) + (28789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132635177 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226122162229 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28789:ℚ)^(-2:ℤ) : ℝ) = ((28789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3135 : ((((45224432687 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28789 < q → q < 28793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28793).mp (by decide +kernel))) hgap
  have hprev := s2L_3134
  have hrat : ((45224432687 : ℚ) / 100000000000) ≤ ((14132635177 : ℚ) / 31250000000) + (28793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224432687 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14132635177 : ℚ) / 31250000000) : ℚ) : ℝ) + ((28793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28793:ℚ)^(-2:ℤ) : ℝ) = ((28793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3136 : ((((18089773123 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28793 < q → q < 28807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28807).mp (by decide +kernel))) hgap
  have hprev := s2L_3135
  have hrat : ((18089773123 : ℚ) / 40000000000) ≤ ((45224432687 : ℚ) / 100000000000) + (28807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089773123 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((45224432687 : ℚ) / 100000000000) : ℚ) : ℝ) + ((28807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28807:ℚ)^(-2:ℤ) : ℝ) = ((28807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3137 : ((((452244329279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28807 < q → q < 28813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28813).mp (by decide +kernel))) hgap
  have hprev := s2L_3136
  have hrat : ((452244329279 : ℚ) / 1000000000000) ≤ ((18089773123 : ℚ) / 40000000000) + (28813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244329279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089773123 : ℚ) / 40000000000) : ℚ) : ℝ) + ((28813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28813:ℚ)^(-2:ℤ) : ℝ) = ((28813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3138 : ((((452244330483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28813 < q → q < 28817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28817).mp (by decide +kernel))) hgap
  have hprev := s2L_3137
  have hrat : ((452244330483 : ℚ) / 1000000000000) ≤ ((452244329279 : ℚ) / 1000000000000) + (28817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244330483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244329279 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28817:ℚ)^(-2:ℤ) : ℝ) = ((28817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3139 : ((((90448866337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28817 < q → q < 28837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28837).mp (by decide +kernel))) hgap
  have hprev := s2L_3138
  have hrat : ((90448866337 : ℚ) / 200000000000) ≤ ((452244330483 : ℚ) / 1000000000000) + (28837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448866337 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452244330483 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28837:ℚ)^(-2:ℤ) : ℝ) = ((28837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3140 : ((((452244332887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28837 < q → q < 28843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28843).mp (by decide +kernel))) hgap
  have hprev := s2L_3139
  have hrat : ((452244332887 : ℚ) / 1000000000000) ≤ ((90448866337 : ℚ) / 200000000000) + (28843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244332887 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448866337 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28843:ℚ)^(-2:ℤ) : ℝ) = ((28843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3141 : ((((452244334087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28843 < q → q < 28859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28859).mp (by decide +kernel))) hgap
  have hprev := s2L_3140
  have hrat : ((452244334087 : ℚ) / 1000000000000) ≤ ((452244332887 : ℚ) / 1000000000000) + (28859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244334087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244332887 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28859:ℚ)^(-2:ℤ) : ℝ) = ((28859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3142 : ((((452244335287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28859 < q → q < 28867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28867).mp (by decide +kernel))) hgap
  have hprev := s2L_3141
  have hrat : ((452244335287 : ℚ) / 1000000000000) ≤ ((452244334087 : ℚ) / 1000000000000) + (28867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244335287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244334087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28867:ℚ)^(-2:ℤ) : ℝ) = ((28867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3143 : ((((226122168243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28867 < q → q < 28871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28871).mp (by decide +kernel))) hgap
  have hprev := s2L_3142
  have hrat : ((226122168243 : ℚ) / 500000000000) ≤ ((452244335287 : ℚ) / 1000000000000) + (28871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122168243 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244335287 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28871:ℚ)^(-2:ℤ) : ℝ) = ((28871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3144 : ((((90448867537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28871 < q → q < 28879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28879).mp (by decide +kernel))) hgap
  have hprev := s2L_3143
  have hrat : ((90448867537 : ℚ) / 200000000000) ≤ ((226122168243 : ℚ) / 500000000000) + (28879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448867537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226122168243 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28879:ℚ)^(-2:ℤ) : ℝ) = ((28879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3145 : ((((226122169441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28879 < q → q < 28901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28901).mp (by decide +kernel))) hgap
  have hprev := s2L_3144
  have hrat : ((226122169441 : ℚ) / 500000000000) ≤ ((90448867537 : ℚ) / 200000000000) + (28901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122169441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448867537 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28901:ℚ)^(-2:ℤ) : ℝ) = ((28901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3146 : ((((226122170039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28901 < q → q < 28909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28909).mp (by decide +kernel))) hgap
  have hprev := s2L_3145
  have hrat : ((226122170039 : ℚ) / 500000000000) ≤ ((226122169441 : ℚ) / 500000000000) + (28909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122170039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122169441 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28909:ℚ)^(-2:ℤ) : ℝ) = ((28909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3147 : ((((452244341273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28909 < q → q < 28921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28921).mp (by decide +kernel))) hgap
  have hprev := s2L_3146
  have hrat : ((452244341273 : ℚ) / 1000000000000) ≤ ((226122170039 : ℚ) / 500000000000) + (28921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244341273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122170039 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28921:ℚ)^(-2:ℤ) : ℝ) = ((28921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3148 : ((((113061085617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28921 < q → q < 28927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28927).mp (by decide +kernel))) hgap
  have hprev := s2L_3147
  have hrat : ((113061085617 : ℚ) / 250000000000) ≤ ((452244341273 : ℚ) / 1000000000000) + (28927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061085617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244341273 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28927:ℚ)^(-2:ℤ) : ℝ) = ((28927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3149 : ((((226122171831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28927 < q → q < 28933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28933).mp (by decide +kernel))) hgap
  have hprev := s2L_3148
  have hrat : ((226122171831 : ℚ) / 500000000000) ≤ ((113061085617 : ℚ) / 250000000000) + (28933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122171831 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061085617 : ℚ) / 250000000000) : ℚ) : ℝ) + ((28933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28933:ℚ)^(-2:ℤ) : ℝ) = ((28933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3150 : ((((90448868971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28933 < q → q < 28949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28949).mp (by decide +kernel))) hgap
  have hprev := s2L_3149
  have hrat : ((90448868971 : ℚ) / 200000000000) ≤ ((226122171831 : ℚ) / 500000000000) + (28949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448868971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226122171831 : ℚ) / 500000000000) : ℚ) : ℝ) + ((28949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28949:ℚ)^(-2:ℤ) : ℝ) = ((28949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3151 : ((((452244346047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28949 < q → q < 28961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28961).mp (by decide +kernel))) hgap
  have hprev := s2L_3150
  have hrat : ((452244346047 : ℚ) / 1000000000000) ≤ ((90448868971 : ℚ) / 200000000000) + (28961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244346047 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448868971 : ℚ) / 200000000000) : ℚ) : ℝ) + ((28961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28961:ℚ)^(-2:ℤ) : ℝ) = ((28961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3152 : ((((452244347237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 28979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28961 < q → q < 28979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 28979).mp (by decide +kernel))) hgap
  have hprev := s2L_3151
  have hrat : ((452244347237 : ℚ) / 1000000000000) ≤ ((452244346047 : ℚ) / 1000000000000) + (28979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244347237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244346047 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((28979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((28979:ℚ)^(-2:ℤ) : ℝ) = ((28979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3153 : ((((18089773937 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 28979 < q → q < 29009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29009).mp (by decide +kernel))) hgap
  have hprev := s2L_3152
  have hrat : ((18089773937 : ℚ) / 40000000000) ≤ ((452244347237 : ℚ) / 1000000000000) + (29009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089773937 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244347237 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29009:ℚ)^(-2:ℤ) : ℝ) = ((29009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3154 : ((((113061087403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29009 < q → q < 29017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29017).mp (by decide +kernel))) hgap
  have hprev := s2L_3153
  have hrat : ((113061087403 : ℚ) / 250000000000) ≤ ((18089773937 : ℚ) / 40000000000) + (29017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061087403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18089773937 : ℚ) / 40000000000) : ℚ) : ℝ) + ((29017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29017:ℚ)^(-2:ℤ) : ℝ) = ((29017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3155 : ((((452244350799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29017 < q → q < 29021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29021).mp (by decide +kernel))) hgap
  have hprev := s2L_3154
  have hrat : ((452244350799 : ℚ) / 1000000000000) ≤ ((113061087403 : ℚ) / 250000000000) + (29021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244350799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061087403 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29021:ℚ)^(-2:ℤ) : ℝ) = ((29021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3156 : ((((226122175993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29021 < q → q < 29023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29023).mp (by decide +kernel))) hgap
  have hprev := s2L_3155
  have hrat : ((226122175993 : ℚ) / 500000000000) ≤ ((452244350799 : ℚ) / 1000000000000) + (29023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122175993 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244350799 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29023:ℚ)^(-2:ℤ) : ℝ) = ((29023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3157 : ((((113061088293 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29023 < q → q < 29027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29027).mp (by decide +kernel))) hgap
  have hprev := s2L_3156
  have hrat : ((113061088293 : ℚ) / 250000000000) ≤ ((226122175993 : ℚ) / 500000000000) + (29027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061088293 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122175993 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29027:ℚ)^(-2:ℤ) : ℝ) = ((29027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3158 : ((((226122177179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29027 < q → q < 29033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29033).mp (by decide +kernel))) hgap
  have hprev := s2L_3157
  have hrat : ((226122177179 : ℚ) / 500000000000) ≤ ((113061088293 : ℚ) / 250000000000) + (29033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122177179 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061088293 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29033:ℚ)^(-2:ℤ) : ℝ) = ((29033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3159 : ((((226122177771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29033 < q → q < 29059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29059).mp (by decide +kernel))) hgap
  have hprev := s2L_3158
  have hrat : ((226122177771 : ℚ) / 500000000000) ≤ ((226122177179 : ℚ) / 500000000000) + (29059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122177771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122177179 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29059:ℚ)^(-2:ℤ) : ℝ) = ((29059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3160 : ((((18089774269 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29059 < q → q < 29063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29063).mp (by decide +kernel))) hgap
  have hprev := s2L_3159
  have hrat : ((18089774269 : ℚ) / 40000000000) ≤ ((226122177771 : ℚ) / 500000000000) + (29063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089774269 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226122177771 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29063:ℚ)^(-2:ℤ) : ℝ) = ((29063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3161 : ((((452244357907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29063 < q → q < 29077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29077).mp (by decide +kernel))) hgap
  have hprev := s2L_3160
  have hrat : ((452244357907 : ℚ) / 1000000000000) ≤ ((18089774269 : ℚ) / 40000000000) + (29077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244357907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089774269 : ℚ) / 40000000000) : ℚ) : ℝ) + ((29077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29077:ℚ)^(-2:ℤ) : ℝ) = ((29077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3162 : ((((452244359087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29077 < q → q < 29101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29101).mp (by decide +kernel))) hgap
  have hprev := s2L_3161
  have hrat : ((452244359087 : ℚ) / 1000000000000) ≤ ((452244357907 : ℚ) / 1000000000000) + (29101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244359087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244357907 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29101:ℚ)^(-2:ℤ) : ℝ) = ((29101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3163 : ((((226122180133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29101 < q → q < 29123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29123).mp (by decide +kernel))) hgap
  have hprev := s2L_3162
  have hrat : ((226122180133 : ℚ) / 500000000000) ≤ ((452244359087 : ℚ) / 1000000000000) + (29123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122180133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244359087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29123:ℚ)^(-2:ℤ) : ℝ) = ((29123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3164 : ((((113061090361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29123 < q → q < 29129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29129).mp (by decide +kernel))) hgap
  have hprev := s2L_3163
  have hrat : ((113061090361 : ℚ) / 250000000000) ≤ ((226122180133 : ℚ) / 500000000000) + (29129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061090361 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122180133 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29129:ℚ)^(-2:ℤ) : ℝ) = ((29129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3165 : ((((226122181311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29129 < q → q < 29131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29131).mp (by decide +kernel))) hgap
  have hprev := s2L_3164
  have hrat : ((226122181311 : ℚ) / 500000000000) ≤ ((113061090361 : ℚ) / 250000000000) + (29131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122181311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061090361 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29131:ℚ)^(-2:ℤ) : ℝ) = ((29131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3166 : ((((452244363799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29131 < q → q < 29137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29137).mp (by decide +kernel))) hgap
  have hprev := s2L_3165
  have hrat : ((452244363799 : ℚ) / 1000000000000) ≤ ((226122181311 : ℚ) / 500000000000) + (29137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244363799 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122181311 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29137:ℚ)^(-2:ℤ) : ℝ) = ((29137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3167 : ((((28265272811 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29137 < q → q < 29147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29147).mp (by decide +kernel))) hgap
  have hprev := s2L_3166
  have hrat : ((28265272811 : ℚ) / 62500000000) ≤ ((452244363799 : ℚ) / 1000000000000) + (29147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265272811 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452244363799 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29147:ℚ)^(-2:ℤ) : ℝ) = ((29147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3168 : ((((56530545769 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29147 < q → q < 29153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29153).mp (by decide +kernel))) hgap
  have hprev := s2L_3167
  have hrat : ((56530545769 : ℚ) / 125000000000) ≤ ((28265272811 : ℚ) / 62500000000) + (29153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530545769 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28265272811 : ℚ) / 62500000000) : ℚ) : ℝ) + ((29153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29153:ℚ)^(-2:ℤ) : ℝ) = ((29153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3169 : ((((452244367327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29153 < q → q < 29167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29167).mp (by decide +kernel))) hgap
  have hprev := s2L_3168
  have hrat : ((452244367327 : ℚ) / 1000000000000) ≤ ((56530545769 : ℚ) / 125000000000) + (29167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244367327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530545769 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29167:ℚ)^(-2:ℤ) : ℝ) = ((29167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3170 : ((((452244368501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29167 < q → q < 29173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29173).mp (by decide +kernel))) hgap
  have hprev := s2L_3169
  have hrat : ((452244368501 : ℚ) / 1000000000000) ≤ ((452244367327 : ℚ) / 1000000000000) + (29173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244368501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244367327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29173:ℚ)^(-2:ℤ) : ℝ) = ((29173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3171 : ((((18089774787 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29173 < q → q < 29179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29179).mp (by decide +kernel))) hgap
  have hprev := s2L_3170
  have hrat : ((18089774787 : ℚ) / 40000000000) ≤ ((452244368501 : ℚ) / 1000000000000) + (29179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089774787 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244368501 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29179:ℚ)^(-2:ℤ) : ℝ) = ((29179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3172 : ((((14132636589 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29179 < q → q < 29191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29191).mp (by decide +kernel))) hgap
  have hprev := s2L_3171
  have hrat : ((14132636589 : ℚ) / 31250000000) ≤ ((18089774787 : ℚ) / 40000000000) + (29191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132636589 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((18089774787 : ℚ) / 40000000000) : ℚ) : ℝ) + ((29191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29191:ℚ)^(-2:ℤ) : ℝ) = ((29191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3173 : ((((22612218601 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29191 < q → q < 29201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29201).mp (by decide +kernel))) hgap
  have hprev := s2L_3172
  have hrat : ((22612218601 : ℚ) / 50000000000) ≤ ((14132636589 : ℚ) / 31250000000) + (29201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612218601 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14132636589 : ℚ) / 31250000000) : ℚ) : ℝ) + ((29201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29201:ℚ)^(-2:ℤ) : ℝ) = ((29201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3174 : ((((56530546649 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29201 < q → q < 29207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29207).mp (by decide +kernel))) hgap
  have hprev := s2L_3173
  have hrat : ((56530546649 : ℚ) / 125000000000) ≤ ((22612218601 : ℚ) / 50000000000) + (29207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530546649 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22612218601 : ℚ) / 50000000000) : ℚ) : ℝ) + ((29207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29207:ℚ)^(-2:ℤ) : ℝ) = ((29207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3175 : ((((113061093591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29207 < q → q < 29209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29209).mp (by decide +kernel))) hgap
  have hprev := s2L_3174
  have hrat : ((113061093591 : ℚ) / 250000000000) ≤ ((56530546649 : ℚ) / 125000000000) + (29209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061093591 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530546649 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29209:ℚ)^(-2:ℤ) : ℝ) = ((29209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3176 : ((((90448875107 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29209 < q → q < 29221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29221).mp (by decide +kernel))) hgap
  have hprev := s2L_3175
  have hrat : ((90448875107 : ℚ) / 200000000000) ≤ ((113061093591 : ℚ) / 250000000000) + (29221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448875107 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113061093591 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29221:ℚ)^(-2:ℤ) : ℝ) = ((29221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3177 : ((((90448875341 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29221 < q → q < 29231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29231).mp (by decide +kernel))) hgap
  have hprev := s2L_3176
  have hrat : ((90448875341 : ℚ) / 200000000000) ≤ ((90448875107 : ℚ) / 200000000000) + (29231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448875341 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448875107 : ℚ) / 200000000000) : ℚ) : ℝ) + ((29231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29231:ℚ)^(-2:ℤ) : ℝ) = ((29231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3178 : ((((226122188937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29231 < q → q < 29243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29243).mp (by decide +kernel))) hgap
  have hprev := s2L_3177
  have hrat : ((226122188937 : ℚ) / 500000000000) ≤ ((90448875341 : ℚ) / 200000000000) + (29243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122188937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448875341 : ℚ) / 200000000000) : ℚ) : ℝ) + ((29243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29243:ℚ)^(-2:ℤ) : ℝ) = ((29243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3179 : ((((226122189521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29243 < q → q < 29251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29251).mp (by decide +kernel))) hgap
  have hprev := s2L_3178
  have hrat : ((226122189521 : ℚ) / 500000000000) ≤ ((226122188937 : ℚ) / 500000000000) + (29251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122189521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122188937 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29251:ℚ)^(-2:ℤ) : ℝ) = ((29251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3180 : ((((452244380209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29251 < q → q < 29269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29269).mp (by decide +kernel))) hgap
  have hprev := s2L_3179
  have hrat : ((452244380209 : ℚ) / 1000000000000) ≤ ((226122189521 : ℚ) / 500000000000) + (29269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244380209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122189521 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29269:ℚ)^(-2:ℤ) : ℝ) = ((29269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3181 : ((((226122190687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29269 < q → q < 29287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29287).mp (by decide +kernel))) hgap
  have hprev := s2L_3180
  have hrat : ((226122190687 : ℚ) / 500000000000) ≤ ((452244380209 : ℚ) / 1000000000000) + (29287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122190687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244380209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29287:ℚ)^(-2:ℤ) : ℝ) = ((29287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3182 : ((((452244382539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29287 < q → q < 29297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29297).mp (by decide +kernel))) hgap
  have hprev := s2L_3181
  have hrat : ((452244382539 : ℚ) / 1000000000000) ≤ ((226122190687 : ℚ) / 500000000000) + (29297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244382539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122190687 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29297:ℚ)^(-2:ℤ) : ℝ) = ((29297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3183 : ((((452244383703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29297 < q → q < 29303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29303).mp (by decide +kernel))) hgap
  have hprev := s2L_3182
  have hrat : ((452244383703 : ℚ) / 1000000000000) ≤ ((452244382539 : ℚ) / 1000000000000) + (29303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244383703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244382539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29303:ℚ)^(-2:ℤ) : ℝ) = ((29303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3184 : ((((226122192433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29303 < q → q < 29311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29311).mp (by decide +kernel))) hgap
  have hprev := s2L_3183
  have hrat : ((226122192433 : ℚ) / 500000000000) ≤ ((452244383703 : ℚ) / 1000000000000) + (29311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122192433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244383703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29311:ℚ)^(-2:ℤ) : ℝ) = ((29311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3185 : ((((113061096507 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29311 < q → q < 29327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29327).mp (by decide +kernel))) hgap
  have hprev := s2L_3184
  have hrat : ((113061096507 : ℚ) / 250000000000) ≤ ((226122192433 : ℚ) / 500000000000) + (29327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061096507 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122192433 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29327:ℚ)^(-2:ℤ) : ℝ) = ((29327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3186 : ((((45224438719 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29327 < q → q < 29333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29333).mp (by decide +kernel))) hgap
  have hprev := s2L_3185
  have hrat : ((45224438719 : ℚ) / 100000000000) ≤ ((113061096507 : ℚ) / 250000000000) + (29333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224438719 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113061096507 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29333:ℚ)^(-2:ℤ) : ℝ) = ((29333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3187 : ((((452244388351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29333 < q → q < 29339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29339).mp (by decide +kernel))) hgap
  have hprev := s2L_3186
  have hrat : ((452244388351 : ℚ) / 1000000000000) ≤ ((45224438719 : ℚ) / 100000000000) + (29339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244388351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224438719 : ℚ) / 100000000000) : ℚ) : ℝ) + ((29339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29339:ℚ)^(-2:ℤ) : ℝ) = ((29339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3188 : ((((56530548689 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29339 < q → q < 29347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29347).mp (by decide +kernel))) hgap
  have hprev := s2L_3187
  have hrat : ((56530548689 : ℚ) / 125000000000) ≤ ((452244388351 : ℚ) / 1000000000000) + (29347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530548689 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244388351 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29347:ℚ)^(-2:ℤ) : ℝ) = ((29347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3189 : ((((452244390671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29363, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29347 < q → q < 29363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29363).mp (by decide +kernel))) hgap
  have hprev := s2L_3188
  have hrat : ((452244390671 : ℚ) / 1000000000000) ≤ ((56530548689 : ℚ) / 125000000000) + (29363:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244390671 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530548689 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29363:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29363:ℚ)^(-2:ℤ) : ℝ) = ((29363:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3190 : ((((452244391829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29363 < q → q < 29383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29383).mp (by decide +kernel))) hgap
  have hprev := s2L_3189
  have hrat : ((452244391829 : ℚ) / 1000000000000) ≤ ((452244390671 : ℚ) / 1000000000000) + (29383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244391829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244390671 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29383:ℚ)^(-2:ℤ) : ℝ) = ((29383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3191 : ((((226122196493 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29383 < q → q < 29387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29387).mp (by decide +kernel))) hgap
  have hprev := s2L_3190
  have hrat : ((226122196493 : ℚ) / 500000000000) ≤ ((452244391829 : ℚ) / 1000000000000) + (29387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122196493 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244391829 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29387:ℚ)^(-2:ℤ) : ℝ) = ((29387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3192 : ((((452244394143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29387 < q → q < 29389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29389).mp (by decide +kernel))) hgap
  have hprev := s2L_3191
  have hrat : ((452244394143 : ℚ) / 1000000000000) ≤ ((226122196493 : ℚ) / 500000000000) + (29389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244394143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122196493 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29389:ℚ)^(-2:ℤ) : ℝ) = ((29389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3193 : ((((4522443953 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29389 < q → q < 29399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29399).mp (by decide +kernel))) hgap
  have hprev := s2L_3192
  have hrat : ((4522443953 : ℚ) / 10000000000) ≤ ((452244394143 : ℚ) / 1000000000000) + (29399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522443953 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452244394143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29399:ℚ)^(-2:ℤ) : ℝ) = ((29399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3194 : ((((56530549557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29399 < q → q < 29401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29401).mp (by decide +kernel))) hgap
  have hprev := s2L_3193
  have hrat : ((56530549557 : ℚ) / 125000000000) ≤ ((4522443953 : ℚ) / 10000000000) + (29401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530549557 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4522443953 : ℚ) / 10000000000) : ℚ) : ℝ) + ((29401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29401:ℚ)^(-2:ℤ) : ℝ) = ((29401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3195 : ((((113061099403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29401 < q → q < 29411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29411).mp (by decide +kernel))) hgap
  have hprev := s2L_3194
  have hrat : ((113061099403 : ℚ) / 250000000000) ≤ ((56530549557 : ℚ) / 125000000000) + (29411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061099403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530549557 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29411:ℚ)^(-2:ℤ) : ℝ) = ((29411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3196 : ((((452244398767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29411 < q → q < 29423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29423).mp (by decide +kernel))) hgap
  have hprev := s2L_3195
  have hrat : ((452244398767 : ℚ) / 1000000000000) ≤ ((113061099403 : ℚ) / 250000000000) + (29423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244398767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061099403 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29423:ℚ)^(-2:ℤ) : ℝ) = ((29423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3197 : ((((452244399921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29423 < q → q < 29429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29429).mp (by decide +kernel))) hgap
  have hprev := s2L_3196
  have hrat : ((452244399921 : ℚ) / 1000000000000) ≤ ((452244398767 : ℚ) / 1000000000000) + (29429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244399921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244398767 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29429:ℚ)^(-2:ℤ) : ℝ) = ((29429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3198 : ((((18089776043 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29429 < q → q < 29437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29437).mp (by decide +kernel))) hgap
  have hprev := s2L_3197
  have hrat : ((18089776043 : ℚ) / 40000000000) ≤ ((452244399921 : ℚ) / 1000000000000) + (29437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089776043 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244399921 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29437:ℚ)^(-2:ℤ) : ℝ) = ((29437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3199 : ((((113061100557 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29437 < q → q < 29443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29443).mp (by decide +kernel))) hgap
  have hprev := s2L_3198
  have hrat : ((113061100557 : ℚ) / 250000000000) ≤ ((18089776043 : ℚ) / 40000000000) + (29443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061100557 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18089776043 : ℚ) / 40000000000) : ℚ) : ℝ) + ((29443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29443:ℚ)^(-2:ℤ) : ℝ) = ((29443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3200 : ((((22612220169 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29443 < q → q < 29453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29453).mp (by decide +kernel))) hgap
  have hprev := s2L_3199
  have hrat : ((22612220169 : ℚ) / 50000000000) ≤ ((113061100557 : ℚ) / 250000000000) + (29453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612220169 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113061100557 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29453:ℚ)^(-2:ℤ) : ℝ) = ((29453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3201 : ((((452244404531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29453 < q → q < 29473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29473).mp (by decide +kernel))) hgap
  have hprev := s2L_3200
  have hrat : ((452244404531 : ℚ) / 1000000000000) ≤ ((22612220169 : ℚ) / 50000000000) + (29473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244404531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612220169 : ℚ) / 50000000000) : ℚ) : ℝ) + ((29473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29473:ℚ)^(-2:ℤ) : ℝ) = ((29473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3202 : ((((452244405681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29473 < q → q < 29483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29483).mp (by decide +kernel))) hgap
  have hprev := s2L_3201
  have hrat : ((452244405681 : ℚ) / 1000000000000) ≤ ((452244404531 : ℚ) / 1000000000000) + (29483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244405681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244404531 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29483:ℚ)^(-2:ℤ) : ℝ) = ((29483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3203 : ((((45224440683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29483 < q → q < 29501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29501).mp (by decide +kernel))) hgap
  have hprev := s2L_3202
  have hrat : ((45224440683 : ℚ) / 100000000000) ≤ ((452244405681 : ℚ) / 1000000000000) + (29501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224440683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452244405681 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29501:ℚ)^(-2:ℤ) : ℝ) = ((29501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3204 : ((((56530550997 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29501 < q → q < 29527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29527).mp (by decide +kernel))) hgap
  have hprev := s2L_3203
  have hrat : ((56530550997 : ℚ) / 125000000000) ≤ ((45224440683 : ℚ) / 100000000000) + (29527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530550997 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45224440683 : ℚ) / 100000000000) : ℚ) : ℝ) + ((29527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29527:ℚ)^(-2:ℤ) : ℝ) = ((29527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3205 : ((((226122204561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29527 < q → q < 29531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29531).mp (by decide +kernel))) hgap
  have hprev := s2L_3204
  have hrat : ((226122204561 : ℚ) / 500000000000) ≤ ((56530550997 : ℚ) / 125000000000) + (29531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122204561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530550997 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29531:ℚ)^(-2:ℤ) : ℝ) = ((29531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3206 : ((((113061102567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29531 < q → q < 29537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29537).mp (by decide +kernel))) hgap
  have hprev := s2L_3205
  have hrat : ((113061102567 : ℚ) / 250000000000) ≤ ((226122204561 : ℚ) / 500000000000) + (29537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061102567 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122204561 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29537:ℚ)^(-2:ℤ) : ℝ) = ((29537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3207 : ((((452244411411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29537 < q → q < 29567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29567).mp (by decide +kernel))) hgap
  have hprev := s2L_3206
  have hrat : ((452244411411 : ℚ) / 1000000000000) ≤ ((113061102567 : ℚ) / 250000000000) + (29567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244411411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061102567 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29567:ℚ)^(-2:ℤ) : ℝ) = ((29567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3208 : ((((226122206277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29567 < q → q < 29569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29569).mp (by decide +kernel))) hgap
  have hprev := s2L_3207
  have hrat : ((226122206277 : ℚ) / 500000000000) ≤ ((452244411411 : ℚ) / 1000000000000) + (29569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122206277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244411411 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29569:ℚ)^(-2:ℤ) : ℝ) = ((29569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3209 : ((((452244413697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29569 < q → q < 29573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29573).mp (by decide +kernel))) hgap
  have hprev := s2L_3208
  have hrat : ((452244413697 : ℚ) / 1000000000000) ≤ ((226122206277 : ℚ) / 500000000000) + (29573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244413697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122206277 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29573:ℚ)^(-2:ℤ) : ℝ) = ((29573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3210 : ((((452244414839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29573 < q → q < 29581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29581).mp (by decide +kernel))) hgap
  have hprev := s2L_3209
  have hrat : ((452244414839 : ℚ) / 1000000000000) ≤ ((452244413697 : ℚ) / 1000000000000) + (29581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244414839 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244413697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29581:ℚ)^(-2:ℤ) : ℝ) = ((29581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3211 : ((((452244415981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29581 < q → q < 29587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29587).mp (by decide +kernel))) hgap
  have hprev := s2L_3210
  have hrat : ((452244415981 : ℚ) / 1000000000000) ≤ ((452244414839 : ℚ) / 1000000000000) + (29587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244415981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244414839 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29587:ℚ)^(-2:ℤ) : ℝ) = ((29587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3212 : ((((226122208561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29587 < q → q < 29599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29599).mp (by decide +kernel))) hgap
  have hprev := s2L_3211
  have hrat : ((226122208561 : ℚ) / 500000000000) ≤ ((452244415981 : ℚ) / 1000000000000) + (29599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122208561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244415981 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29599:ℚ)^(-2:ℤ) : ℝ) = ((29599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3213 : ((((226122209131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29599 < q → q < 29611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29611).mp (by decide +kernel))) hgap
  have hprev := s2L_3212
  have hrat : ((226122209131 : ℚ) / 500000000000) ≤ ((226122208561 : ℚ) / 500000000000) + (29611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122209131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226122208561 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29611:ℚ)^(-2:ℤ) : ℝ) = ((29611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3214 : ((((452244419401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29611 < q → q < 29629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29629).mp (by decide +kernel))) hgap
  have hprev := s2L_3213
  have hrat : ((452244419401 : ℚ) / 1000000000000) ≤ ((226122209131 : ℚ) / 500000000000) + (29629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244419401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122209131 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29629:ℚ)^(-2:ℤ) : ℝ) = ((29629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3215 : ((((452244420539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29629 < q → q < 29633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29633).mp (by decide +kernel))) hgap
  have hprev := s2L_3214
  have hrat : ((452244420539 : ℚ) / 1000000000000) ≤ ((452244419401 : ℚ) / 1000000000000) + (29633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244420539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244419401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29633:ℚ)^(-2:ℤ) : ℝ) = ((29633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3216 : ((((452244421677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29633 < q → q < 29641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29641).mp (by decide +kernel))) hgap
  have hprev := s2L_3215
  have hrat : ((452244421677 : ℚ) / 1000000000000) ≤ ((452244420539 : ℚ) / 1000000000000) + (29641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244421677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244420539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29641:ℚ)^(-2:ℤ) : ℝ) = ((29641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3217 : ((((452244422813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29641 < q → q < 29663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29663).mp (by decide +kernel))) hgap
  have hprev := s2L_3216
  have hrat : ((452244422813 : ℚ) / 1000000000000) ≤ ((452244421677 : ℚ) / 1000000000000) + (29663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244422813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244421677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29663:ℚ)^(-2:ℤ) : ℝ) = ((29663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3218 : ((((452244423949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29663 < q → q < 29669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29669).mp (by decide +kernel))) hgap
  have hprev := s2L_3217
  have hrat : ((452244423949 : ℚ) / 1000000000000) ≤ ((452244422813 : ℚ) / 1000000000000) + (29669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244423949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244422813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29669:ℚ)^(-2:ℤ) : ℝ) = ((29669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3219 : ((((113061106271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29669 < q → q < 29671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29671).mp (by decide +kernel))) hgap
  have hprev := s2L_3218
  have hrat : ((113061106271 : ℚ) / 250000000000) ≤ ((452244423949 : ℚ) / 1000000000000) + (29671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061106271 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452244423949 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29671:ℚ)^(-2:ℤ) : ℝ) = ((29671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3220 : ((((226122213109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29671 < q → q < 29683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29683).mp (by decide +kernel))) hgap
  have hprev := s2L_3219
  have hrat : ((226122213109 : ℚ) / 500000000000) ≤ ((113061106271 : ℚ) / 250000000000) + (29683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122213109 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113061106271 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29683:ℚ)^(-2:ℤ) : ℝ) = ((29683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3221 : ((((9044888547 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29683 < q → q < 29717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29717).mp (by decide +kernel))) hgap
  have hprev := s2L_3220
  have hrat : ((9044888547 : ℚ) / 20000000000) ≤ ((226122213109 : ℚ) / 500000000000) + (29717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044888547 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226122213109 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29717:ℚ)^(-2:ℤ) : ℝ) = ((29717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3222 : ((((452244428481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29717 < q → q < 29723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29723).mp (by decide +kernel))) hgap
  have hprev := s2L_3221
  have hrat : ((452244428481 : ℚ) / 1000000000000) ≤ ((9044888547 : ℚ) / 20000000000) + (29723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244428481 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044888547 : ℚ) / 20000000000) : ℚ) : ℝ) + ((29723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29723:ℚ)^(-2:ℤ) : ℝ) = ((29723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3223 : ((((452244429611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29723 < q → q < 29741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29741).mp (by decide +kernel))) hgap
  have hprev := s2L_3222
  have hrat : ((452244429611 : ℚ) / 1000000000000) ≤ ((452244428481 : ℚ) / 1000000000000) + (29741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244429611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244428481 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29741:ℚ)^(-2:ℤ) : ℝ) = ((29741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3224 : ((((22612221537 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29741 < q → q < 29753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29753).mp (by decide +kernel))) hgap
  have hprev := s2L_3223
  have hrat : ((22612221537 : ℚ) / 50000000000) ≤ ((452244429611 : ℚ) / 1000000000000) + (29753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612221537 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452244429611 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29753:ℚ)^(-2:ℤ) : ℝ) = ((29753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3225 : ((((452244431869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29753 < q → q < 29759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29759).mp (by decide +kernel))) hgap
  have hprev := s2L_3224
  have hrat : ((452244431869 : ℚ) / 1000000000000) ≤ ((22612221537 : ℚ) / 50000000000) + (29759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244431869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612221537 : ℚ) / 50000000000) : ℚ) : ℝ) + ((29759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29759:ℚ)^(-2:ℤ) : ℝ) = ((29759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3226 : ((((226122216499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29759 < q → q < 29761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29761).mp (by decide +kernel))) hgap
  have hprev := s2L_3225
  have hrat : ((226122216499 : ℚ) / 500000000000) ≤ ((452244431869 : ℚ) / 1000000000000) + (29761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122216499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244431869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29761:ℚ)^(-2:ℤ) : ℝ) = ((29761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3227 : ((((113061108531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29761 < q → q < 29789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29789).mp (by decide +kernel))) hgap
  have hprev := s2L_3226
  have hrat : ((113061108531 : ℚ) / 250000000000) ≤ ((226122216499 : ℚ) / 500000000000) + (29789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113061108531 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226122216499 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29789:ℚ)^(-2:ℤ) : ℝ) = ((29789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3228 : ((((452244435249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29789 < q → q < 29803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29803).mp (by decide +kernel))) hgap
  have hprev := s2L_3227
  have hrat : ((452244435249 : ℚ) / 1000000000000) ≤ ((113061108531 : ℚ) / 250000000000) + (29803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244435249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113061108531 : ℚ) / 250000000000) : ℚ) : ℝ) + ((29803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29803:ℚ)^(-2:ℤ) : ℝ) = ((29803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3229 : ((((452244436373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29803 < q → q < 29819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29819).mp (by decide +kernel))) hgap
  have hprev := s2L_3228
  have hrat : ((452244436373 : ℚ) / 1000000000000) ≤ ((452244435249 : ℚ) / 1000000000000) + (29819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244436373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244435249 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29819:ℚ)^(-2:ℤ) : ℝ) = ((29819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3230 : ((((56530554687 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29819 < q → q < 29833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29833).mp (by decide +kernel))) hgap
  have hprev := s2L_3229
  have hrat : ((56530554687 : ℚ) / 125000000000) ≤ ((452244436373 : ℚ) / 1000000000000) + (29833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530554687 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452244436373 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29833:ℚ)^(-2:ℤ) : ℝ) = ((29833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3231 : ((((452244438619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29833 < q → q < 29837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29837).mp (by decide +kernel))) hgap
  have hprev := s2L_3230
  have hrat : ((452244438619 : ℚ) / 1000000000000) ≤ ((56530554687 : ℚ) / 125000000000) + (29837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244438619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530554687 : ℚ) / 125000000000) : ℚ) : ℝ) + ((29837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29837:ℚ)^(-2:ℤ) : ℝ) = ((29837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3232 : ((((452244439741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29837 < q → q < 29851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29851).mp (by decide +kernel))) hgap
  have hprev := s2L_3231
  have hrat : ((452244439741 : ℚ) / 1000000000000) ≤ ((452244438619 : ℚ) / 1000000000000) + (29851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244439741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244438619 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29851:ℚ)^(-2:ℤ) : ℝ) = ((29851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3233 : ((((226122220431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29851 < q → q < 29863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29863).mp (by decide +kernel))) hgap
  have hprev := s2L_3232
  have hrat : ((226122220431 : ℚ) / 500000000000) ≤ ((452244439741 : ℚ) / 1000000000000) + (29863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122220431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244439741 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29863:ℚ)^(-2:ℤ) : ℝ) = ((29863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3234 : ((((452244441983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29863 < q → q < 29867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29867).mp (by decide +kernel))) hgap
  have hprev := s2L_3233
  have hrat : ((452244441983 : ℚ) / 1000000000000) ≤ ((226122220431 : ℚ) / 500000000000) + (29867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244441983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122220431 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29867:ℚ)^(-2:ℤ) : ℝ) = ((29867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3235 : ((((452244443103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29867 < q → q < 29873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29873).mp (by decide +kernel))) hgap
  have hprev := s2L_3234
  have hrat : ((452244443103 : ℚ) / 1000000000000) ≤ ((452244441983 : ℚ) / 1000000000000) + (29873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244443103 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244441983 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29873:ℚ)^(-2:ℤ) : ℝ) = ((29873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3236 : ((((452244444223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29873 < q → q < 29879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29879).mp (by decide +kernel))) hgap
  have hprev := s2L_3235
  have hrat : ((452244444223 : ℚ) / 1000000000000) ≤ ((452244443103 : ℚ) / 1000000000000) + (29879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244444223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244443103 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29879:ℚ)^(-2:ℤ) : ℝ) = ((29879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3237 : ((((226122222671 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29879 < q → q < 29881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29881).mp (by decide +kernel))) hgap
  have hprev := s2L_3236
  have hrat : ((226122222671 : ℚ) / 500000000000) ≤ ((452244444223 : ℚ) / 1000000000000) + (29881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122222671 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244444223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29881:ℚ)^(-2:ℤ) : ℝ) = ((29881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3238 : ((((452244446459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29881 < q → q < 29917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29917).mp (by decide +kernel))) hgap
  have hprev := s2L_3237
  have hrat : ((452244446459 : ℚ) / 1000000000000) ≤ ((226122222671 : ℚ) / 500000000000) + (29917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244446459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226122222671 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29917:ℚ)^(-2:ℤ) : ℝ) = ((29917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3239 : ((((18089777903 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29917 < q → q < 29921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29921).mp (by decide +kernel))) hgap
  have hprev := s2L_3238
  have hrat : ((18089777903 : ℚ) / 40000000000) ≤ ((452244446459 : ℚ) / 1000000000000) + (29921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089777903 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452244446459 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29921:ℚ)^(-2:ℤ) : ℝ) = ((29921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3240 : ((((452244448691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29921 < q → q < 29927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29927).mp (by decide +kernel))) hgap
  have hprev := s2L_3239
  have hrat : ((452244448691 : ℚ) / 1000000000000) ≤ ((18089777903 : ℚ) / 40000000000) + (29927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244448691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089777903 : ℚ) / 40000000000) : ℚ) : ℝ) + ((29927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29927:ℚ)^(-2:ℤ) : ℝ) = ((29927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3241 : ((((226122224903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29927 < q → q < 29947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29947).mp (by decide +kernel))) hgap
  have hprev := s2L_3240
  have hrat : ((226122224903 : ℚ) / 500000000000) ≤ ((452244448691 : ℚ) / 1000000000000) + (29947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122224903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244448691 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((29947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29947:ℚ)^(-2:ℤ) : ℝ) = ((29947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3242 : ((((11306111273 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29947 < q → q < 29959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29959).mp (by decide +kernel))) hgap
  have hprev := s2L_3241
  have hrat : ((11306111273 : ℚ) / 25000000000) ≤ ((226122224903 : ℚ) / 500000000000) + (29959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306111273 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226122224903 : ℚ) / 500000000000) : ℚ) : ℝ) + ((29959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29959:ℚ)^(-2:ℤ) : ℝ) = ((29959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3243 : ((((7066319563 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29959 < q → q < 29983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29983).mp (by decide +kernel))) hgap
  have hprev := s2L_3242
  have hrat : ((7066319563 : ℚ) / 15625000000) ≤ ((11306111273 : ℚ) / 25000000000) + (29983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066319563 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((11306111273 : ℚ) / 25000000000) : ℚ) : ℝ) + ((29983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29983:ℚ)^(-2:ℤ) : ℝ) = ((29983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3244 : ((((452244453143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 29989, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29983 < q → q < 29989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 29989).mp (by decide +kernel))) hgap
  have hprev := s2L_3243
  have hrat : ((452244453143 : ℚ) / 1000000000000) ≤ ((7066319563 : ℚ) / 15625000000) + (29989:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244453143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066319563 : ℚ) / 15625000000) : ℚ) : ℝ) + ((29989:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((29989:ℚ)^(-2:ℤ) : ℝ) = ((29989:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3245 : ((((452244454253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 30011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 29989 < q → q < 30011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30011).mp (by decide +kernel))) hgap
  have hprev := s2L_3244
  have hrat : ((452244454253 : ℚ) / 1000000000000) ≤ ((452244453143 : ℚ) / 1000000000000) + (30011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244454253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244453143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((30011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((30011:ℚ)^(-2:ℤ) : ℝ) = ((30011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3246 : ((((452244455363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 30013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 30011 < q → q < 30013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30013).mp (by decide +kernel))) hgap
  have hprev := s2L_3245
  have hrat : ((452244455363 : ℚ) / 1000000000000) ≤ ((452244454253 : ℚ) / 1000000000000) + (30013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244455363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244454253 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((30013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((30013:ℚ)^(-2:ℤ) : ℝ) = ((30013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3247 : ((((452244456471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 30029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 30013 < q → q < 30029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30029).mp (by decide +kernel))) hgap
  have hprev := s2L_3246
  have hrat : ((452244456471 : ℚ) / 1000000000000) ≤ ((452244455363 : ℚ) / 1000000000000) + (30029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452244456471 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452244455363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((30029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((30029:ℚ)^(-2:ℤ) : ℝ) = ((30029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_3248 : ((((226122228789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 30047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 30029 < q → q < 30047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 30047).mp (by decide +kernel))) hgap
  have hprev := s2L_3247
  have hrat : ((226122228789 : ℚ) / 500000000000) ≤ ((452244456471 : ℚ) / 1000000000000) + (30047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226122228789 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452244456471 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((30047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((30047:ℚ)^(-2:ℤ) : ℝ) = ((30047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))

end

end Work.RHContract.RegionI
