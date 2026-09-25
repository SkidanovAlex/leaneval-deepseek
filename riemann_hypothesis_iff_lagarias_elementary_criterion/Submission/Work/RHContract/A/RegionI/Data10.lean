import Mathlib
import Submission.Work.RHContract.A.RegionI.Data09

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma s2L_1602 : ((((452240364207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13523 < q → q < 13537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13537).mp (by decide +kernel))) hgap
  have hprev := s2L_1601
  have hrat : ((452240364207 : ℚ) / 1000000000000) ≤ ((361792287 : ℚ) / 800000000) + (13537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240364207 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((361792287 : ℚ) / 800000000) : ℚ) : ℝ) + ((13537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13537:ℚ)^(-2:ℤ) : ℝ) = ((13537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1603 : ((((452240369651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13537 < q → q < 13553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13553).mp (by decide +kernel))) hgap
  have hprev := s2L_1602
  have hrat : ((452240369651 : ℚ) / 1000000000000) ≤ ((452240364207 : ℚ) / 1000000000000) + (13553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240369651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240364207 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13553:ℚ)^(-2:ℤ) : ℝ) = ((13553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1604 : ((((452240375083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13553 < q → q < 13567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13567).mp (by decide +kernel))) hgap
  have hprev := s2L_1603
  have hrat : ((452240375083 : ℚ) / 1000000000000) ≤ ((452240369651 : ℚ) / 1000000000000) + (13567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240375083 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240369651 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13567:ℚ)^(-2:ℤ) : ℝ) = ((13567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1605 : ((((452240380507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13567 < q → q < 13577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13577).mp (by decide +kernel))) hgap
  have hprev := s2L_1604
  have hrat : ((452240380507 : ℚ) / 1000000000000) ≤ ((452240375083 : ℚ) / 1000000000000) + (13577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240380507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240375083 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13577:ℚ)^(-2:ℤ) : ℝ) = ((13577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1606 : ((((706625603 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13577 < q → q < 13591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13591).mp (by decide +kernel))) hgap
  have hprev := s2L_1605
  have hrat : ((706625603 : ℚ) / 1562500000) ≤ ((452240380507 : ℚ) / 1000000000000) + (13591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((706625603 : ℚ) / 1562500000) : ℚ) : ℝ) ≤ ((((452240380507 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13591:ℚ)^(-2:ℤ) : ℝ) = ((13591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1607 : ((((14132512229 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13591 < q → q < 13597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13597).mp (by decide +kernel))) hgap
  have hprev := s2L_1606
  have hrat : ((14132512229 : ℚ) / 31250000000) ≤ ((706625603 : ℚ) / 1562500000) + (13597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132512229 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((706625603 : ℚ) / 1562500000) : ℚ) : ℝ) + ((13597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13597:ℚ)^(-2:ℤ) : ℝ) = ((13597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1608 : ((((113060099181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13597 < q → q < 13613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13613).mp (by decide +kernel))) hgap
  have hprev := s2L_1607
  have hrat : ((113060099181 : ℚ) / 250000000000) ≤ ((14132512229 : ℚ) / 31250000000) + (13613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060099181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14132512229 : ℚ) / 31250000000) : ℚ) : ℝ) + ((13613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13613:ℚ)^(-2:ℤ) : ℝ) = ((13613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1609 : ((((90448080423 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13613 < q → q < 13619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13619).mp (by decide +kernel))) hgap
  have hprev := s2L_1608
  have hrat : ((90448080423 : ℚ) / 200000000000) ≤ ((113060099181 : ℚ) / 250000000000) + (13619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448080423 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060099181 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13619:ℚ)^(-2:ℤ) : ℝ) = ((13619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1610 : ((((180896163 : ℚ) / 400000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13619 < q → q < 13627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13627).mp (by decide +kernel))) hgap
  have hprev := s2L_1609
  have hrat : ((180896163 : ℚ) / 400000000) ≤ ((90448080423 : ℚ) / 200000000000) + (13627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((180896163 : ℚ) / 400000000) : ℚ) : ℝ) ≤ ((((90448080423 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13627:ℚ)^(-2:ℤ) : ℝ) = ((13627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1611 : ((((5653005161 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13627 < q → q < 13633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13633).mp (by decide +kernel))) hgap
  have hprev := s2L_1610
  have hrat : ((5653005161 : ℚ) / 12500000000) ≤ ((180896163 : ℚ) / 400000000) + (13633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653005161 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((180896163 : ℚ) / 400000000) : ℚ) : ℝ) + ((13633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13633:ℚ)^(-2:ℤ) : ℝ) = ((13633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1612 : ((((452240418247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13633 < q → q < 13649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13649).mp (by decide +kernel))) hgap
  have hprev := s2L_1611
  have hrat : ((452240418247 : ℚ) / 1000000000000) ≤ ((5653005161 : ℚ) / 12500000000) + (13649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240418247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5653005161 : ℚ) / 12500000000) : ℚ) : ℝ) + ((13649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13649:ℚ)^(-2:ℤ) : ℝ) = ((13649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1613 : ((((452240423599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13649 < q → q < 13669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13669).mp (by decide +kernel))) hgap
  have hprev := s2L_1612
  have hrat : ((452240423599 : ℚ) / 1000000000000) ≤ ((452240418247 : ℚ) / 1000000000000) + (13669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240423599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240418247 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13669:ℚ)^(-2:ℤ) : ℝ) = ((13669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1614 : ((((452240428943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13669 < q → q < 13679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13679).mp (by decide +kernel))) hgap
  have hprev := s2L_1613
  have hrat : ((452240428943 : ℚ) / 1000000000000) ≤ ((452240423599 : ℚ) / 1000000000000) + (13679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240428943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240423599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13679:ℚ)^(-2:ℤ) : ℝ) = ((13679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1615 : ((((90448086857 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13679 < q → q < 13681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13681).mp (by decide +kernel))) hgap
  have hprev := s2L_1614
  have hrat : ((90448086857 : ℚ) / 200000000000) ≤ ((452240428943 : ℚ) / 1000000000000) + (13681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448086857 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240428943 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13681:ℚ)^(-2:ℤ) : ℝ) = ((13681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1616 : ((((452240439623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13681 < q → q < 13687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13687).mp (by decide +kernel))) hgap
  have hprev := s2L_1615
  have hrat : ((452240439623 : ℚ) / 1000000000000) ≤ ((90448086857 : ℚ) / 200000000000) + (13687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240439623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448086857 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13687:ℚ)^(-2:ℤ) : ℝ) = ((13687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1617 : ((((452240444957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13687 < q → q < 13691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13691).mp (by decide +kernel))) hgap
  have hprev := s2L_1616
  have hrat : ((452240444957 : ℚ) / 1000000000000) ≤ ((452240439623 : ℚ) / 1000000000000) + (13691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240444957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240439623 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13691:ℚ)^(-2:ℤ) : ℝ) = ((13691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1618 : ((((45224045029 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13691 < q → q < 13693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13693).mp (by decide +kernel))) hgap
  have hprev := s2L_1617
  have hrat : ((45224045029 : ℚ) / 100000000000) ≤ ((452240444957 : ℚ) / 1000000000000) + (13693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224045029 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240444957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13693:ℚ)^(-2:ℤ) : ℝ) = ((13693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1619 : ((((22612022781 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13693 < q → q < 13697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13697).mp (by decide +kernel))) hgap
  have hprev := s2L_1618
  have hrat : ((22612022781 : ℚ) / 50000000000) ≤ ((45224045029 : ℚ) / 100000000000) + (13697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612022781 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((45224045029 : ℚ) / 100000000000) : ℚ) : ℝ) + ((13697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13697:ℚ)^(-2:ℤ) : ℝ) = ((13697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1620 : ((((22612023047 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13697 < q → q < 13709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13709).mp (by decide +kernel))) hgap
  have hprev := s2L_1619
  have hrat : ((22612023047 : ℚ) / 50000000000) ≤ ((22612022781 : ℚ) / 50000000000) + (13709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612023047 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((22612022781 : ℚ) / 50000000000) : ℚ) : ℝ) + ((13709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13709:ℚ)^(-2:ℤ) : ℝ) = ((13709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1621 : ((((452240466259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13709 < q → q < 13711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13711).mp (by decide +kernel))) hgap
  have hprev := s2L_1620
  have hrat : ((452240466259 : ℚ) / 1000000000000) ≤ ((22612023047 : ℚ) / 50000000000) + (13711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240466259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612023047 : ℚ) / 50000000000) : ℚ) : ℝ) + ((13711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13711:ℚ)^(-2:ℤ) : ℝ) = ((13711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1622 : ((((45224047157 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13711 < q → q < 13721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13721).mp (by decide +kernel))) hgap
  have hprev := s2L_1621
  have hrat : ((45224047157 : ℚ) / 100000000000) ≤ ((452240466259 : ℚ) / 1000000000000) + (13721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224047157 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240466259 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13721:ℚ)^(-2:ℤ) : ℝ) = ((13721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1623 : ((((5653005961 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13721 < q → q < 13723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13723).mp (by decide +kernel))) hgap
  have hprev := s2L_1622
  have hrat : ((5653005961 : ℚ) / 12500000000) ≤ ((45224047157 : ℚ) / 100000000000) + (13723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653005961 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((45224047157 : ℚ) / 100000000000) : ℚ) : ℝ) + ((13723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13723:ℚ)^(-2:ℤ) : ℝ) = ((13723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1624 : ((((90448096437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13723 < q → q < 13729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13729).mp (by decide +kernel))) hgap
  have hprev := s2L_1623
  have hrat : ((90448096437 : ℚ) / 200000000000) ≤ ((5653005961 : ℚ) / 12500000000) + (13729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448096437 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5653005961 : ℚ) / 12500000000) : ℚ) : ℝ) + ((13729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13729:ℚ)^(-2:ℤ) : ℝ) = ((13729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1625 : ((((452240487473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13729 < q → q < 13751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13751).mp (by decide +kernel))) hgap
  have hprev := s2L_1624
  have hrat : ((452240487473 : ℚ) / 1000000000000) ≤ ((90448096437 : ℚ) / 200000000000) + (13751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240487473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448096437 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13751:ℚ)^(-2:ℤ) : ℝ) = ((13751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1626 : ((((113060123189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13751 < q → q < 13757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13757).mp (by decide +kernel))) hgap
  have hprev := s2L_1625
  have hrat : ((113060123189 : ℚ) / 250000000000) ≤ ((452240487473 : ℚ) / 1000000000000) + (13757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060123189 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240487473 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13757:ℚ)^(-2:ℤ) : ℝ) = ((13757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1627 : ((((226120249019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13757 < q → q < 13759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13759).mp (by decide +kernel))) hgap
  have hprev := s2L_1626
  have hrat : ((226120249019 : ℚ) / 500000000000) ≤ ((113060123189 : ℚ) / 250000000000) + (13759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120249019 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060123189 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13759:ℚ)^(-2:ℤ) : ℝ) = ((13759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1628 : ((((452240503317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13759 < q → q < 13763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13763).mp (by decide +kernel))) hgap
  have hprev := s2L_1627
  have hrat : ((452240503317 : ℚ) / 1000000000000) ≤ ((226120249019 : ℚ) / 500000000000) + (13763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240503317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120249019 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13763:ℚ)^(-2:ℤ) : ℝ) = ((13763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1629 : ((((226120254291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13763 < q → q < 13781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13781).mp (by decide +kernel))) hgap
  have hprev := s2L_1628
  have hrat : ((226120254291 : ℚ) / 500000000000) ≤ ((452240503317 : ℚ) / 1000000000000) + (13781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120254291 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240503317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13781:ℚ)^(-2:ℤ) : ℝ) = ((13781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1630 : ((((452240513841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13781 < q → q < 13789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13789).mp (by decide +kernel))) hgap
  have hprev := s2L_1629
  have hrat : ((452240513841 : ℚ) / 1000000000000) ≤ ((226120254291 : ℚ) / 500000000000) + (13789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240513841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120254291 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13789:ℚ)^(-2:ℤ) : ℝ) = ((13789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1631 : ((((113060129773 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13789 < q → q < 13799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13799).mp (by decide +kernel))) hgap
  have hprev := s2L_1630
  have hrat : ((113060129773 : ℚ) / 250000000000) ≤ ((452240513841 : ℚ) / 1000000000000) + (13799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060129773 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240513841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13799:ℚ)^(-2:ℤ) : ℝ) = ((13799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1632 : ((((452240524337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13799 < q → q < 13807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13807).mp (by decide +kernel))) hgap
  have hprev := s2L_1631
  have hrat : ((452240524337 : ℚ) / 1000000000000) ≤ ((113060129773 : ℚ) / 250000000000) + (13807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240524337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060129773 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13807:ℚ)^(-2:ℤ) : ℝ) = ((13807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1633 : ((((90448105913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13807 < q → q < 13829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13829).mp (by decide +kernel))) hgap
  have hprev := s2L_1632
  have hrat : ((90448105913 : ℚ) / 200000000000) ≤ ((452240524337 : ℚ) / 1000000000000) + (13829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448105913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240524337 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13829:ℚ)^(-2:ℤ) : ℝ) = ((13829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1634 : ((((56530066849 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13829 < q → q < 13831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13831).mp (by decide +kernel))) hgap
  have hprev := s2L_1633
  have hrat : ((56530066849 : ℚ) / 125000000000) ≤ ((90448105913 : ℚ) / 200000000000) + (13831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530066849 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90448105913 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13831:ℚ)^(-2:ℤ) : ℝ) = ((13831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1635 : ((((452240540011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13831 < q → q < 13841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13841).mp (by decide +kernel))) hgap
  have hprev := s2L_1634
  have hrat : ((452240540011 : ℚ) / 1000000000000) ≤ ((56530066849 : ℚ) / 125000000000) + (13841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240540011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530066849 : ℚ) / 125000000000) : ℚ) : ℝ) + ((13841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13841:ℚ)^(-2:ℤ) : ℝ) = ((13841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1636 : ((((452240545217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13841 < q → q < 13859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13859).mp (by decide +kernel))) hgap
  have hprev := s2L_1635
  have hrat : ((452240545217 : ℚ) / 1000000000000) ≤ ((452240540011 : ℚ) / 1000000000000) + (13859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240545217 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240540011 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13859:ℚ)^(-2:ℤ) : ℝ) = ((13859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1637 : ((((113060137603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13859 < q → q < 13873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13873).mp (by decide +kernel))) hgap
  have hprev := s2L_1636
  have hrat : ((113060137603 : ℚ) / 250000000000) ≤ ((452240545217 : ℚ) / 1000000000000) + (13873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060137603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240545217 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13873:ℚ)^(-2:ℤ) : ℝ) = ((13873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1638 : ((((113060138901 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13873 < q → q < 13877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13877).mp (by decide +kernel))) hgap
  have hprev := s2L_1637
  have hrat : ((113060138901 : ℚ) / 250000000000) ≤ ((113060137603 : ℚ) / 250000000000) + (13877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060138901 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060137603 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13877:ℚ)^(-2:ℤ) : ℝ) = ((13877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1639 : ((((90448112159 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13877 < q → q < 13879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13879).mp (by decide +kernel))) hgap
  have hprev := s2L_1638
  have hrat : ((90448112159 : ℚ) / 200000000000) ≤ ((113060138901 : ℚ) / 250000000000) + (13879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448112159 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060138901 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13879:ℚ)^(-2:ℤ) : ℝ) = ((13879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1640 : ((((452240565983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13879 < q → q < 13883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13883).mp (by decide +kernel))) hgap
  have hprev := s2L_1639
  have hrat : ((452240565983 : ℚ) / 1000000000000) ≤ ((90448112159 : ℚ) / 200000000000) + (13883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240565983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448112159 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13883:ℚ)^(-2:ℤ) : ℝ) = ((13883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1641 : ((((452240571157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13883 < q → q < 13901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13901).mp (by decide +kernel))) hgap
  have hprev := s2L_1640
  have hrat : ((452240571157 : ℚ) / 1000000000000) ≤ ((452240565983 : ℚ) / 1000000000000) + (13901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240571157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240565983 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13901:ℚ)^(-2:ℤ) : ℝ) = ((13901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1642 : ((((45224057633 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13901 < q → q < 13903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13903).mp (by decide +kernel))) hgap
  have hprev := s2L_1641
  have hrat : ((45224057633 : ℚ) / 100000000000) ≤ ((452240571157 : ℚ) / 1000000000000) + (13903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224057633 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240571157 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13903:ℚ)^(-2:ℤ) : ℝ) = ((13903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1643 : ((((904481163 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13903 < q → q < 13907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13907).mp (by decide +kernel))) hgap
  have hprev := s2L_1642
  have hrat : ((904481163 : ℚ) / 2000000000) ≤ ((45224057633 : ℚ) / 100000000000) + (13907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904481163 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((45224057633 : ℚ) / 100000000000) : ℚ) : ℝ) + ((13907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13907:ℚ)^(-2:ℤ) : ℝ) = ((13907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1644 : ((((226120293333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13907 < q → q < 13913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13913).mp (by decide +kernel))) hgap
  have hprev := s2L_1643
  have hrat : ((226120293333 : ℚ) / 500000000000) ≤ ((904481163 : ℚ) / 2000000000) + (13913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120293333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((904481163 : ℚ) / 2000000000) : ℚ) : ℝ) + ((13913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13913:ℚ)^(-2:ℤ) : ℝ) = ((13913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1645 : ((((226120295913 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13913 < q → q < 13921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13921).mp (by decide +kernel))) hgap
  have hprev := s2L_1644
  have hrat : ((226120295913 : ℚ) / 500000000000) ≤ ((226120293333 : ℚ) / 500000000000) + (13921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120295913 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120293333 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13921:ℚ)^(-2:ℤ) : ℝ) = ((13921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1646 : ((((226120298489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13921 < q → q < 13931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13931).mp (by decide +kernel))) hgap
  have hprev := s2L_1645
  have hrat : ((226120298489 : ℚ) / 500000000000) ≤ ((226120295913 : ℚ) / 500000000000) + (13931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120298489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120295913 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13931:ℚ)^(-2:ℤ) : ℝ) = ((13931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1647 : ((((452240602129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13931 < q → q < 13933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13933).mp (by decide +kernel))) hgap
  have hprev := s2L_1646
  have hrat : ((452240602129 : ℚ) / 1000000000000) ≤ ((226120298489 : ℚ) / 500000000000) + (13933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240602129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120298489 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13933:ℚ)^(-2:ℤ) : ℝ) = ((13933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1648 : ((((226120303629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13933 < q → q < 13963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13963).mp (by decide +kernel))) hgap
  have hprev := s2L_1647
  have hrat : ((226120303629 : ℚ) / 500000000000) ≤ ((452240602129 : ℚ) / 1000000000000) + (13963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120303629 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240602129 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13963:ℚ)^(-2:ℤ) : ℝ) = ((13963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1649 : ((((14132519137 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13963 < q → q < 13967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13967).mp (by decide +kernel))) hgap
  have hprev := s2L_1648
  have hrat : ((14132519137 : ℚ) / 31250000000) ≤ ((226120303629 : ℚ) / 500000000000) + (13967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132519137 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226120303629 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13967:ℚ)^(-2:ℤ) : ℝ) = ((13967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1650 : ((((28265038593 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13967 < q → q < 13997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13997).mp (by decide +kernel))) hgap
  have hprev := s2L_1649
  have hrat : ((28265038593 : ℚ) / 62500000000) ≤ ((14132519137 : ℚ) / 31250000000) + (13997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265038593 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((14132519137 : ℚ) / 31250000000) : ℚ) : ℝ) + ((13997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13997:ℚ)^(-2:ℤ) : ℝ) = ((13997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1651 : ((((45224062259 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13997 < q → q < 13999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13999).mp (by decide +kernel))) hgap
  have hprev := s2L_1650
  have hrat : ((45224062259 : ℚ) / 100000000000) ≤ ((28265038593 : ℚ) / 62500000000) + (13999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224062259 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((28265038593 : ℚ) / 62500000000) : ℚ) : ℝ) + ((13999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13999:ℚ)^(-2:ℤ) : ℝ) = ((13999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1652 : ((((90448125537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13999 < q → q < 14009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14009).mp (by decide +kernel))) hgap
  have hprev := s2L_1651
  have hrat : ((90448125537 : ℚ) / 200000000000) ≤ ((45224062259 : ℚ) / 100000000000) + (14009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448125537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45224062259 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14009:ℚ)^(-2:ℤ) : ℝ) = ((14009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1653 : ((((452240632779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14009 < q → q < 14011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14011).mp (by decide +kernel))) hgap
  have hprev := s2L_1652
  have hrat : ((452240632779 : ℚ) / 1000000000000) ≤ ((90448125537 : ℚ) / 200000000000) + (14011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240632779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448125537 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14011:ℚ)^(-2:ℤ) : ℝ) = ((14011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1654 : ((((452240637859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14011 < q → q < 14029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14029).mp (by decide +kernel))) hgap
  have hprev := s2L_1653
  have hrat : ((452240637859 : ℚ) / 1000000000000) ≤ ((452240632779 : ℚ) / 1000000000000) + (14029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240637859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240632779 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14029:ℚ)^(-2:ℤ) : ℝ) = ((14029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1655 : ((((452240642937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14029 < q → q < 14033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14033).mp (by decide +kernel))) hgap
  have hprev := s2L_1654
  have hrat : ((452240642937 : ℚ) / 1000000000000) ≤ ((452240637859 : ℚ) / 1000000000000) + (14033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240642937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240637859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14033:ℚ)^(-2:ℤ) : ℝ) = ((14033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1656 : ((((226120324001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14033 < q → q < 14051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14051).mp (by decide +kernel))) hgap
  have hprev := s2L_1655
  have hrat : ((226120324001 : ℚ) / 500000000000) ≤ ((452240642937 : ℚ) / 1000000000000) + (14051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120324001 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240642937 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14051:ℚ)^(-2:ℤ) : ℝ) = ((14051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1657 : ((((226120326531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14051 < q → q < 14057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14057).mp (by decide +kernel))) hgap
  have hprev := s2L_1656
  have hrat : ((226120326531 : ℚ) / 500000000000) ≤ ((226120324001 : ℚ) / 500000000000) + (14057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120326531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120324001 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14057:ℚ)^(-2:ℤ) : ℝ) = ((14057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1658 : ((((7066260283 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14057 < q → q < 14071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14071).mp (by decide +kernel))) hgap
  have hprev := s2L_1657
  have hrat : ((7066260283 : ℚ) / 15625000000) ≤ ((226120326531 : ℚ) / 500000000000) + (14071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066260283 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((226120326531 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14071:ℚ)^(-2:ℤ) : ℝ) = ((14071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1659 : ((((90448132631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14071 < q → q < 14081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14081).mp (by decide +kernel))) hgap
  have hprev := s2L_1658
  have hrat : ((90448132631 : ℚ) / 200000000000) ≤ ((7066260283 : ℚ) / 15625000000) + (14081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448132631 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((7066260283 : ℚ) / 15625000000) : ℚ) : ℝ) + ((14081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14081:ℚ)^(-2:ℤ) : ℝ) = ((14081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1660 : ((((452240668197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14081 < q → q < 14083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14083).mp (by decide +kernel))) hgap
  have hprev := s2L_1659
  have hrat : ((452240668197 : ℚ) / 1000000000000) ≤ ((90448132631 : ℚ) / 200000000000) + (14083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240668197 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448132631 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14083:ℚ)^(-2:ℤ) : ℝ) = ((14083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1661 : ((((113060168309 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14083 < q → q < 14087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14087).mp (by decide +kernel))) hgap
  have hprev := s2L_1660
  have hrat : ((113060168309 : ℚ) / 250000000000) ≤ ((452240668197 : ℚ) / 1000000000000) + (14087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060168309 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240668197 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14087:ℚ)^(-2:ℤ) : ℝ) = ((14087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1662 : ((((22612033913 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14087 < q → q < 14107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14107).mp (by decide +kernel))) hgap
  have hprev := s2L_1661
  have hrat : ((22612033913 : ℚ) / 50000000000) ≤ ((113060168309 : ℚ) / 250000000000) + (14107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612033913 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113060168309 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14107:ℚ)^(-2:ℤ) : ℝ) = ((14107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1663 : ((((452240683259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14107 < q → q < 14143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14143).mp (by decide +kernel))) hgap
  have hprev := s2L_1662
  have hrat : ((452240683259 : ℚ) / 1000000000000) ≤ ((22612033913 : ℚ) / 50000000000) + (14143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240683259 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612033913 : ℚ) / 50000000000) : ℚ) : ℝ) + ((14143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14143:ℚ)^(-2:ℤ) : ℝ) = ((14143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1664 : ((((226120344127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14143 < q → q < 14149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14149).mp (by decide +kernel))) hgap
  have hprev := s2L_1663
  have hrat : ((226120344127 : ℚ) / 500000000000) ≤ ((452240683259 : ℚ) / 1000000000000) + (14149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120344127 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240683259 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14149:ℚ)^(-2:ℤ) : ℝ) = ((14149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1665 : ((((226120346623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14149 < q → q < 14153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14153).mp (by decide +kernel))) hgap
  have hprev := s2L_1664
  have hrat : ((226120346623 : ℚ) / 500000000000) ≤ ((226120344127 : ℚ) / 500000000000) + (14153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120346623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120344127 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14153:ℚ)^(-2:ℤ) : ℝ) = ((14153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1666 : ((((226120349117 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14153 < q → q < 14159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14159).mp (by decide +kernel))) hgap
  have hprev := s2L_1665
  have hrat : ((226120349117 : ℚ) / 500000000000) ≤ ((226120346623 : ℚ) / 500000000000) + (14159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120349117 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120346623 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14159:ℚ)^(-2:ℤ) : ℝ) = ((14159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1667 : ((((113060175803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14159 < q → q < 14173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14173).mp (by decide +kernel))) hgap
  have hprev := s2L_1666
  have hrat : ((113060175803 : ℚ) / 250000000000) ≤ ((226120349117 : ℚ) / 500000000000) + (14173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060175803 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120349117 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14173:ℚ)^(-2:ℤ) : ℝ) = ((14173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1668 : ((((452240708187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14173 < q → q < 14177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14177).mp (by decide +kernel))) hgap
  have hprev := s2L_1667
  have hrat : ((452240708187 : ℚ) / 1000000000000) ≤ ((113060175803 : ℚ) / 250000000000) + (14177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240708187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060175803 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14177:ℚ)^(-2:ℤ) : ℝ) = ((14177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1669 : ((((113060178287 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14177 < q → q < 14197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14197).mp (by decide +kernel))) hgap
  have hprev := s2L_1668
  have hrat : ((113060178287 : ℚ) / 250000000000) ≤ ((452240708187 : ℚ) / 1000000000000) + (14197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060178287 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240708187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14197:ℚ)^(-2:ℤ) : ℝ) = ((14197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1670 : ((((226120359051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14197 < q → q < 14207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14207).mp (by decide +kernel))) hgap
  have hprev := s2L_1669
  have hrat : ((226120359051 : ℚ) / 500000000000) ≤ ((113060178287 : ℚ) / 250000000000) + (14207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120359051 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060178287 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14207:ℚ)^(-2:ℤ) : ℝ) = ((14207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1671 : ((((226120361523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14207 < q → q < 14221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14221).mp (by decide +kernel))) hgap
  have hprev := s2L_1670
  have hrat : ((226120361523 : ℚ) / 500000000000) ≤ ((226120359051 : ℚ) / 500000000000) + (14221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120361523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120359051 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14221:ℚ)^(-2:ℤ) : ℝ) = ((14221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1672 : ((((18089629119 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14221 < q → q < 14243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14243).mp (by decide +kernel))) hgap
  have hprev := s2L_1671
  have hrat : ((18089629119 : ℚ) / 40000000000) ≤ ((226120361523 : ℚ) / 500000000000) + (14243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089629119 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226120361523 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14243:ℚ)^(-2:ℤ) : ℝ) = ((14243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1673 : ((((4522407329 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14243 < q → q < 14249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14249).mp (by decide +kernel))) hgap
  have hprev := s2L_1672
  have hrat : ((4522407329 : ℚ) / 10000000000) ≤ ((18089629119 : ℚ) / 40000000000) + (14249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522407329 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((18089629119 : ℚ) / 40000000000) : ℚ) : ℝ) + ((14249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14249:ℚ)^(-2:ℤ) : ℝ) = ((14249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1674 : ((((452240737823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14249 < q → q < 14251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14251).mp (by decide +kernel))) hgap
  have hprev := s2L_1673
  have hrat : ((452240737823 : ℚ) / 1000000000000) ≤ ((4522407329 : ℚ) / 10000000000) + (14251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240737823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522407329 : ℚ) / 10000000000) : ℚ) : ℝ) + ((14251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14251:ℚ)^(-2:ℤ) : ℝ) = ((14251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1675 : ((((226120371363 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14251 < q → q < 14281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14281).mp (by decide +kernel))) hgap
  have hprev := s2L_1674
  have hrat : ((226120371363 : ℚ) / 500000000000) ≤ ((452240737823 : ℚ) / 1000000000000) + (14281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120371363 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240737823 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14281:ℚ)^(-2:ℤ) : ℝ) = ((14281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1676 : ((((452240747621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14281 < q → q < 14293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14293).mp (by decide +kernel))) hgap
  have hprev := s2L_1675
  have hrat : ((452240747621 : ℚ) / 1000000000000) ≤ ((226120371363 : ℚ) / 500000000000) + (14293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240747621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120371363 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14293:ℚ)^(-2:ℤ) : ℝ) = ((14293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1677 : ((((452240752509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14293 < q → q < 14303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14303).mp (by decide +kernel))) hgap
  have hprev := s2L_1676
  have hrat : ((452240752509 : ℚ) / 1000000000000) ≤ ((452240747621 : ℚ) / 1000000000000) + (14303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240752509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240747621 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14303:ℚ)^(-2:ℤ) : ℝ) = ((14303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1678 : ((((56530094673 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14303 < q → q < 14321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14321).mp (by decide +kernel))) hgap
  have hprev := s2L_1677
  have hrat : ((56530094673 : ℚ) / 125000000000) ≤ ((452240752509 : ℚ) / 1000000000000) + (14321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530094673 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240752509 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14321:ℚ)^(-2:ℤ) : ℝ) = ((14321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1679 : ((((226120381129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14321 < q → q < 14323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14323).mp (by decide +kernel))) hgap
  have hprev := s2L_1678
  have hrat : ((226120381129 : ℚ) / 500000000000) ≤ ((56530094673 : ℚ) / 125000000000) + (14323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120381129 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530094673 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14323:ℚ)^(-2:ℤ) : ℝ) = ((14323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1680 : ((((452240767129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14323 < q → q < 14327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14327).mp (by decide +kernel))) hgap
  have hprev := s2L_1679
  have hrat : ((452240767129 : ℚ) / 1000000000000) ≤ ((226120381129 : ℚ) / 500000000000) + (14327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240767129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120381129 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14327:ℚ)^(-2:ℤ) : ℝ) = ((14327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1681 : ((((452240771991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14327 < q → q < 14341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14341).mp (by decide +kernel))) hgap
  have hprev := s2L_1680
  have hrat : ((452240771991 : ℚ) / 1000000000000) ≤ ((452240767129 : ℚ) / 1000000000000) + (14341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240771991 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240767129 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14341:ℚ)^(-2:ℤ) : ℝ) = ((14341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1682 : ((((452240776849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14341 < q → q < 14347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14347).mp (by decide +kernel))) hgap
  have hprev := s2L_1681
  have hrat : ((452240776849 : ℚ) / 1000000000000) ≤ ((452240771991 : ℚ) / 1000000000000) + (14347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240776849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240771991 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14347:ℚ)^(-2:ℤ) : ℝ) = ((14347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1683 : ((((113060195423 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14347 < q → q < 14369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14369).mp (by decide +kernel))) hgap
  have hprev := s2L_1682
  have hrat : ((113060195423 : ℚ) / 250000000000) ≤ ((452240776849 : ℚ) / 1000000000000) + (14369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060195423 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240776849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14369:ℚ)^(-2:ℤ) : ℝ) = ((14369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1684 : ((((452240786523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14369 < q → q < 14387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14387).mp (by decide +kernel))) hgap
  have hprev := s2L_1683
  have hrat : ((452240786523 : ℚ) / 1000000000000) ≤ ((113060195423 : ℚ) / 250000000000) + (14387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240786523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060195423 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14387:ℚ)^(-2:ℤ) : ℝ) = ((14387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1685 : ((((56530098919 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14387 < q → q < 14389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14389).mp (by decide +kernel))) hgap
  have hprev := s2L_1684
  have hrat : ((56530098919 : ℚ) / 125000000000) ≤ ((452240786523 : ℚ) / 1000000000000) + (14389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530098919 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240786523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14389:ℚ)^(-2:ℤ) : ℝ) = ((14389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1686 : ((((452240796173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14389 < q → q < 14401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14401).mp (by decide +kernel))) hgap
  have hprev := s2L_1685
  have hrat : ((452240796173 : ℚ) / 1000000000000) ≤ ((56530098919 : ℚ) / 125000000000) + (14401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240796173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530098919 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14401:ℚ)^(-2:ℤ) : ℝ) = ((14401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1687 : ((((45224080099 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14401 < q → q < 14407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14407).mp (by decide +kernel))) hgap
  have hprev := s2L_1686
  have hrat : ((45224080099 : ℚ) / 100000000000) ≤ ((452240796173 : ℚ) / 1000000000000) + (14407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224080099 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240796173 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14407:ℚ)^(-2:ℤ) : ℝ) = ((14407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1688 : ((((90448161161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14407 < q → q < 14411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14411).mp (by decide +kernel))) hgap
  have hprev := s2L_1687
  have hrat : ((90448161161 : ℚ) / 200000000000) ≤ ((45224080099 : ℚ) / 100000000000) + (14411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448161161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45224080099 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14411:ℚ)^(-2:ℤ) : ℝ) = ((14411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1689 : ((((226120405307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14411 < q → q < 14419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14419).mp (by decide +kernel))) hgap
  have hprev := s2L_1688
  have hrat : ((226120405307 : ℚ) / 500000000000) ≤ ((90448161161 : ℚ) / 200000000000) + (14419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120405307 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448161161 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14419:ℚ)^(-2:ℤ) : ℝ) = ((14419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1690 : ((((452240815421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14419 < q → q < 14423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14423).mp (by decide +kernel))) hgap
  have hprev := s2L_1689
  have hrat : ((452240815421 : ℚ) / 1000000000000) ≤ ((226120405307 : ℚ) / 500000000000) + (14423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240815421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120405307 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14423:ℚ)^(-2:ℤ) : ℝ) = ((14423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1691 : ((((226120410111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14423 < q → q < 14431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14431).mp (by decide +kernel))) hgap
  have hprev := s2L_1690
  have hrat : ((226120410111 : ℚ) / 500000000000) ≤ ((452240815421 : ℚ) / 1000000000000) + (14431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120410111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240815421 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14431:ℚ)^(-2:ℤ) : ℝ) = ((14431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1692 : ((((452240825019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14431 < q → q < 14437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14437).mp (by decide +kernel))) hgap
  have hprev := s2L_1691
  have hrat : ((452240825019 : ℚ) / 1000000000000) ≤ ((226120410111 : ℚ) / 500000000000) + (14437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240825019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120410111 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14437:ℚ)^(-2:ℤ) : ℝ) = ((14437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1693 : ((((45224082981 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14437 < q → q < 14447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14447).mp (by decide +kernel))) hgap
  have hprev := s2L_1692
  have hrat : ((45224082981 : ℚ) / 100000000000) ≤ ((452240825019 : ℚ) / 1000000000000) + (14447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224082981 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240825019 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14447:ℚ)^(-2:ℤ) : ℝ) = ((14447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1694 : ((((452240834599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14447 < q → q < 14449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14449).mp (by decide +kernel))) hgap
  have hprev := s2L_1693
  have hrat : ((452240834599 : ℚ) / 1000000000000) ≤ ((45224082981 : ℚ) / 100000000000) + (14449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240834599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224082981 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14449:ℚ)^(-2:ℤ) : ℝ) = ((14449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1695 : ((((22612041969 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14449 < q → q < 14461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14461).mp (by decide +kernel))) hgap
  have hprev := s2L_1694
  have hrat : ((22612041969 : ℚ) / 50000000000) ≤ ((452240834599 : ℚ) / 1000000000000) + (14461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612041969 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452240834599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14461:ℚ)^(-2:ℤ) : ℝ) = ((14461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1696 : ((((9044816883 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14461 < q → q < 14479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14479).mp (by decide +kernel))) hgap
  have hprev := s2L_1695
  have hrat : ((9044816883 : ℚ) / 20000000000) ≤ ((22612041969 : ℚ) / 50000000000) + (14479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044816883 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((22612041969 : ℚ) / 50000000000) : ℚ) : ℝ) + ((14479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14479:ℚ)^(-2:ℤ) : ℝ) = ((14479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1697 : ((((452240848913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14479 < q → q < 14489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14489).mp (by decide +kernel))) hgap
  have hprev := s2L_1696
  have hrat : ((452240848913 : ℚ) / 1000000000000) ≤ ((9044816883 : ℚ) / 20000000000) + (14489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240848913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044816883 : ℚ) / 20000000000) : ℚ) : ℝ) + ((14489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14489:ℚ)^(-2:ℤ) : ℝ) = ((14489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1698 : ((((452240853667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14489 < q → q < 14503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14503).mp (by decide +kernel))) hgap
  have hprev := s2L_1697
  have hrat : ((452240853667 : ℚ) / 1000000000000) ≤ ((452240848913 : ℚ) / 1000000000000) + (14503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240853667 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240848913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14503:ℚ)^(-2:ℤ) : ℝ) = ((14503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1699 : ((((45224085841 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14503 < q → q < 14519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14519).mp (by decide +kernel))) hgap
  have hprev := s2L_1698
  have hrat : ((45224085841 : ℚ) / 100000000000) ≤ ((452240853667 : ℚ) / 1000000000000) + (14519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224085841 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452240853667 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14519:ℚ)^(-2:ℤ) : ℝ) = ((14519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1700 : ((((56530107893 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14533, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14519 < q → q < 14533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14533).mp (by decide +kernel))) hgap
  have hprev := s2L_1699
  have hrat : ((56530107893 : ℚ) / 125000000000) ≤ ((45224085841 : ℚ) / 100000000000) + (14533:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530107893 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45224085841 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14533:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14533:ℚ)^(-2:ℤ) : ℝ) = ((14533:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1701 : ((((113060216969 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14533 < q → q < 14537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14537).mp (by decide +kernel))) hgap
  have hprev := s2L_1700
  have hrat : ((113060216969 : ℚ) / 250000000000) ≤ ((56530107893 : ℚ) / 125000000000) + (14537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060216969 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530107893 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14537:ℚ)^(-2:ℤ) : ℝ) = ((14537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1702 : ((((113060218151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14537 < q → q < 14543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14543).mp (by decide +kernel))) hgap
  have hprev := s2L_1701
  have hrat : ((113060218151 : ℚ) / 250000000000) ≤ ((113060216969 : ℚ) / 250000000000) + (14543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060218151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060216969 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14543:ℚ)^(-2:ℤ) : ℝ) = ((14543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1703 : ((((28265054833 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14543 < q → q < 14549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14549).mp (by decide +kernel))) hgap
  have hprev := s2L_1702
  have hrat : ((28265054833 : ℚ) / 62500000000) ≤ ((113060218151 : ℚ) / 250000000000) + (14549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265054833 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113060218151 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14549:ℚ)^(-2:ℤ) : ℝ) = ((14549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1704 : ((((9044817641 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14549 < q → q < 14551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14551).mp (by decide +kernel))) hgap
  have hprev := s2L_1703
  have hrat : ((9044817641 : ℚ) / 20000000000) ≤ ((28265054833 : ℚ) / 62500000000) + (14551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044817641 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((28265054833 : ℚ) / 62500000000) : ℚ) : ℝ) + ((14551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14551:ℚ)^(-2:ℤ) : ℝ) = ((14551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1705 : ((((452240886769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14551 < q → q < 14557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14557).mp (by decide +kernel))) hgap
  have hprev := s2L_1704
  have hrat : ((452240886769 : ℚ) / 1000000000000) ≤ ((9044817641 : ℚ) / 20000000000) + (14557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240886769 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044817641 : ℚ) / 20000000000) : ℚ) : ℝ) + ((14557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14557:ℚ)^(-2:ℤ) : ℝ) = ((14557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1706 : ((((90448178297 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14557 < q → q < 14561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14561).mp (by decide +kernel))) hgap
  have hprev := s2L_1705
  have hrat : ((90448178297 : ℚ) / 200000000000) ≤ ((452240886769 : ℚ) / 1000000000000) + (14561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448178297 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240886769 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14561:ℚ)^(-2:ℤ) : ℝ) = ((14561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1707 : ((((2261204481 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14561 < q → q < 14563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14563).mp (by decide +kernel))) hgap
  have hprev := s2L_1706
  have hrat : ((2261204481 : ℚ) / 5000000000) ≤ ((90448178297 : ℚ) / 200000000000) + (14563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261204481 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((90448178297 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14563:ℚ)^(-2:ℤ) : ℝ) = ((14563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1708 : ((((452240900897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14563 < q → q < 14591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14591).mp (by decide +kernel))) hgap
  have hprev := s2L_1707
  have hrat : ((452240900897 : ℚ) / 1000000000000) ≤ ((2261204481 : ℚ) / 5000000000) + (14591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240900897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2261204481 : ℚ) / 5000000000) : ℚ) : ℝ) + ((14591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14591:ℚ)^(-2:ℤ) : ℝ) = ((14591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1709 : ((((56530113199 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14591 < q → q < 14593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14593).mp (by decide +kernel))) hgap
  have hprev := s2L_1708
  have hrat : ((56530113199 : ℚ) / 125000000000) ≤ ((452240900897 : ℚ) / 1000000000000) + (14593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530113199 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240900897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14593:ℚ)^(-2:ℤ) : ℝ) = ((14593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1710 : ((((452240910269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14593 < q → q < 14621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14621).mp (by decide +kernel))) hgap
  have hprev := s2L_1709
  have hrat : ((452240910269 : ℚ) / 1000000000000) ≤ ((56530113199 : ℚ) / 125000000000) + (14621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240910269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530113199 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14621:ℚ)^(-2:ℤ) : ℝ) = ((14621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1711 : ((((452240914943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14621 < q → q < 14627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14627).mp (by decide +kernel))) hgap
  have hprev := s2L_1710
  have hrat : ((452240914943 : ℚ) / 1000000000000) ≤ ((452240910269 : ℚ) / 1000000000000) + (14627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240914943 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240910269 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14627:ℚ)^(-2:ℤ) : ℝ) = ((14627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1712 : ((((90448183923 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14627 < q → q < 14629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14629).mp (by decide +kernel))) hgap
  have hprev := s2L_1711
  have hrat : ((90448183923 : ℚ) / 200000000000) ≤ ((452240914943 : ℚ) / 1000000000000) + (14629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448183923 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240914943 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14629:ℚ)^(-2:ℤ) : ℝ) = ((14629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1713 : ((((90448184857 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14629 < q → q < 14633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14633).mp (by decide +kernel))) hgap
  have hprev := s2L_1712
  have hrat : ((90448184857 : ℚ) / 200000000000) ≤ ((90448183923 : ℚ) / 200000000000) + (14633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448184857 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448183923 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14633:ℚ)^(-2:ℤ) : ℝ) = ((14633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1714 : ((((452240928951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14633 < q → q < 14639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14639).mp (by decide +kernel))) hgap
  have hprev := s2L_1713
  have hrat : ((452240928951 : ℚ) / 1000000000000) ≤ ((90448184857 : ℚ) / 200000000000) + (14639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240928951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448184857 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14639:ℚ)^(-2:ℤ) : ℝ) = ((14639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1715 : ((((56530116701 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14639 < q → q < 14653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14653).mp (by decide +kernel))) hgap
  have hprev := s2L_1714
  have hrat : ((56530116701 : ℚ) / 125000000000) ≤ ((452240928951 : ℚ) / 1000000000000) + (14653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530116701 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240928951 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14653:ℚ)^(-2:ℤ) : ℝ) = ((14653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1716 : ((((226120469131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14653 < q → q < 14657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14657).mp (by decide +kernel))) hgap
  have hprev := s2L_1715
  have hrat : ((226120469131 : ℚ) / 500000000000) ≤ ((56530116701 : ℚ) / 125000000000) + (14657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120469131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530116701 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14657:ℚ)^(-2:ℤ) : ℝ) = ((14657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1717 : ((((452240942909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14657 < q → q < 14669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14669).mp (by decide +kernel))) hgap
  have hprev := s2L_1716
  have hrat : ((452240942909 : ℚ) / 1000000000000) ≤ ((226120469131 : ℚ) / 500000000000) + (14669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240942909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120469131 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14669:ℚ)^(-2:ℤ) : ℝ) = ((14669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1718 : ((((452240947547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14669 < q → q < 14683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14683).mp (by decide +kernel))) hgap
  have hprev := s2L_1717
  have hrat : ((452240947547 : ℚ) / 1000000000000) ≤ ((452240942909 : ℚ) / 1000000000000) + (14683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240947547 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240942909 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14683:ℚ)^(-2:ℤ) : ℝ) = ((14683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1719 : ((((18089638087 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14683 < q → q < 14699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14699).mp (by decide +kernel))) hgap
  have hprev := s2L_1718
  have hrat : ((18089638087 : ℚ) / 40000000000) ≤ ((452240947547 : ℚ) / 1000000000000) + (14699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089638087 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452240947547 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14699:ℚ)^(-2:ℤ) : ℝ) = ((14699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1720 : ((((226120478397 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14699 < q → q < 14713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14713).mp (by decide +kernel))) hgap
  have hprev := s2L_1719
  have hrat : ((226120478397 : ℚ) / 500000000000) ≤ ((18089638087 : ℚ) / 40000000000) + (14713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120478397 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089638087 : ℚ) / 40000000000) : ℚ) : ℝ) + ((14713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14713:ℚ)^(-2:ℤ) : ℝ) = ((14713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1721 : ((((452240961411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14713 < q → q < 14717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14717).mp (by decide +kernel))) hgap
  have hprev := s2L_1720
  have hrat : ((452240961411 : ℚ) / 1000000000000) ≤ ((226120478397 : ℚ) / 500000000000) + (14717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240961411 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120478397 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14717:ℚ)^(-2:ℤ) : ℝ) = ((14717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1722 : ((((56530120753 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14717 < q → q < 14723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14723).mp (by decide +kernel))) hgap
  have hprev := s2L_1721
  have hrat : ((56530120753 : ℚ) / 125000000000) ≤ ((452240961411 : ℚ) / 1000000000000) + (14723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530120753 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240961411 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14723:ℚ)^(-2:ℤ) : ℝ) = ((14723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1723 : ((((56530121329 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14723 < q → q < 14731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14731).mp (by decide +kernel))) hgap
  have hprev := s2L_1722
  have hrat : ((56530121329 : ℚ) / 125000000000) ≤ ((56530120753 : ℚ) / 125000000000) + (14731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530121329 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((56530120753 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14731:ℚ)^(-2:ℤ) : ℝ) = ((14731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1724 : ((((113060243809 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14731 < q → q < 14737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14737).mp (by decide +kernel))) hgap
  have hprev := s2L_1723
  have hrat : ((113060243809 : ℚ) / 250000000000) ≤ ((56530121329 : ℚ) / 125000000000) + (14737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060243809 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530121329 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14737:ℚ)^(-2:ℤ) : ℝ) = ((14737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1725 : ((((452240979837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14737 < q → q < 14741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14741).mp (by decide +kernel))) hgap
  have hprev := s2L_1724
  have hrat : ((452240979837 : ℚ) / 1000000000000) ≤ ((113060243809 : ℚ) / 250000000000) + (14741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240979837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060243809 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14741:ℚ)^(-2:ℤ) : ℝ) = ((14741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1726 : ((((90448196887 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14741 < q → q < 14747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14747).mp (by decide +kernel))) hgap
  have hprev := s2L_1725
  have hrat : ((90448196887 : ℚ) / 200000000000) ≤ ((452240979837 : ℚ) / 1000000000000) + (14747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448196887 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240979837 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14747:ℚ)^(-2:ℤ) : ℝ) = ((14747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1727 : ((((452240989029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14747 < q → q < 14753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14753).mp (by decide +kernel))) hgap
  have hprev := s2L_1726
  have hrat : ((452240989029 : ℚ) / 1000000000000) ≤ ((90448196887 : ℚ) / 200000000000) + (14753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240989029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448196887 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14753:ℚ)^(-2:ℤ) : ℝ) = ((14753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1728 : ((((452240993619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14753 < q → q < 14759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14759).mp (by decide +kernel))) hgap
  have hprev := s2L_1727
  have hrat : ((452240993619 : ℚ) / 1000000000000) ≤ ((452240989029 : ℚ) / 1000000000000) + (14759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240993619 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240989029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14759:ℚ)^(-2:ℤ) : ℝ) = ((14759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1729 : ((((113060249551 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14759 < q → q < 14767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14767).mp (by decide +kernel))) hgap
  have hprev := s2L_1728
  have hrat : ((113060249551 : ℚ) / 250000000000) ≤ ((452240993619 : ℚ) / 1000000000000) + (14767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060249551 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240993619 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14767:ℚ)^(-2:ℤ) : ℝ) = ((14767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1730 : ((((452241002787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14771, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14767 < q → q < 14771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14771).mp (by decide +kernel))) hgap
  have hprev := s2L_1729
  have hrat : ((452241002787 : ℚ) / 1000000000000) ≤ ((113060249551 : ℚ) / 250000000000) + (14771:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241002787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060249551 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14771:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14771:ℚ)^(-2:ℤ) : ℝ) = ((14771:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1731 : ((((90448201473 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14771 < q → q < 14779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14779).mp (by decide +kernel))) hgap
  have hprev := s2L_1730
  have hrat : ((90448201473 : ℚ) / 200000000000) ≤ ((452241002787 : ℚ) / 1000000000000) + (14779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448201473 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241002787 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14779:ℚ)^(-2:ℤ) : ℝ) = ((14779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1732 : ((((22612050597 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14779 < q → q < 14783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14783).mp (by decide +kernel))) hgap
  have hprev := s2L_1731
  have hrat : ((22612050597 : ℚ) / 50000000000) ≤ ((90448201473 : ℚ) / 200000000000) + (14783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612050597 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((90448201473 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14783:ℚ)^(-2:ℤ) : ℝ) = ((14783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1733 : ((((452241016507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14783 < q → q < 14797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14797).mp (by decide +kernel))) hgap
  have hprev := s2L_1732
  have hrat : ((452241016507 : ℚ) / 1000000000000) ≤ ((22612050597 : ℚ) / 50000000000) + (14797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241016507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612050597 : ℚ) / 50000000000) : ℚ) : ℝ) + ((14797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14797:ℚ)^(-2:ℤ) : ℝ) = ((14797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1734 : ((((56530127633 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14797 < q → q < 14813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14813).mp (by decide +kernel))) hgap
  have hprev := s2L_1733
  have hrat : ((56530127633 : ℚ) / 125000000000) ≤ ((452241016507 : ℚ) / 1000000000000) + (14813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530127633 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452241016507 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14813:ℚ)^(-2:ℤ) : ℝ) = ((14813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1735 : ((((28265064101 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14813 < q → q < 14821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14821).mp (by decide +kernel))) hgap
  have hprev := s2L_1734
  have hrat : ((28265064101 : ℚ) / 62500000000) ≤ ((56530127633 : ℚ) / 125000000000) + (14821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265064101 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56530127633 : ℚ) / 125000000000) : ℚ) : ℝ) + ((14821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14821:ℚ)^(-2:ℤ) : ℝ) = ((14821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1736 : ((((113060257541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14821 < q → q < 14827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14827).mp (by decide +kernel))) hgap
  have hprev := s2L_1735
  have hrat : ((113060257541 : ℚ) / 250000000000) ≤ ((28265064101 : ℚ) / 62500000000) + (14827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060257541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28265064101 : ℚ) / 62500000000) : ℚ) : ℝ) + ((14827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14827:ℚ)^(-2:ℤ) : ℝ) = ((14827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1737 : ((((45224103471 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14827 < q → q < 14831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14831).mp (by decide +kernel))) hgap
  have hprev := s2L_1736
  have hrat : ((45224103471 : ℚ) / 100000000000) ≤ ((113060257541 : ℚ) / 250000000000) + (14831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224103471 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060257541 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14831:ℚ)^(-2:ℤ) : ℝ) = ((14831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1738 : ((((28265064953 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14831 < q → q < 14843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14843).mp (by decide +kernel))) hgap
  have hprev := s2L_1737
  have hrat : ((28265064953 : ℚ) / 62500000000) ≤ ((45224103471 : ℚ) / 100000000000) + (14843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265064953 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((45224103471 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14843:ℚ)^(-2:ℤ) : ℝ) = ((14843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1739 : ((((226120521891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14843 < q → q < 14851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14851).mp (by decide +kernel))) hgap
  have hprev := s2L_1738
  have hrat : ((226120521891 : ℚ) / 500000000000) ≤ ((28265064953 : ℚ) / 62500000000) + (14851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120521891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265064953 : ℚ) / 62500000000) : ℚ) : ℝ) + ((14851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14851:ℚ)^(-2:ℤ) : ℝ) = ((14851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1740 : ((((226120524153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14851 < q → q < 14867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14867).mp (by decide +kernel))) hgap
  have hprev := s2L_1739
  have hrat : ((226120524153 : ℚ) / 500000000000) ≤ ((226120521891 : ℚ) / 500000000000) + (14867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120524153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120521891 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14867:ℚ)^(-2:ℤ) : ℝ) = ((14867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1741 : ((((452241052829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14869, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14867 < q → q < 14869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14869).mp (by decide +kernel))) hgap
  have hprev := s2L_1740
  have hrat : ((452241052829 : ℚ) / 1000000000000) ≤ ((226120524153 : ℚ) / 500000000000) + (14869:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241052829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120524153 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14869:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14869:ℚ)^(-2:ℤ) : ℝ) = ((14869:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1742 : ((((226120528673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14869 < q → q < 14879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14879).mp (by decide +kernel))) hgap
  have hprev := s2L_1741
  have hrat : ((226120528673 : ℚ) / 500000000000) ≤ ((452241052829 : ℚ) / 1000000000000) + (14879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120528673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241052829 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14879:ℚ)^(-2:ℤ) : ℝ) = ((14879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1743 : ((((226120530929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14879 < q → q < 14887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14887).mp (by decide +kernel))) hgap
  have hprev := s2L_1742
  have hrat : ((226120530929 : ℚ) / 500000000000) ≤ ((226120528673 : ℚ) / 500000000000) + (14887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120530929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120528673 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14887:ℚ)^(-2:ℤ) : ℝ) = ((14887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1744 : ((((452241066367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14891, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14887 < q → q < 14891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14891).mp (by decide +kernel))) hgap
  have hprev := s2L_1743
  have hrat : ((452241066367 : ℚ) / 1000000000000) ≤ ((226120530929 : ℚ) / 500000000000) + (14891:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241066367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120530929 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14891:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14891:ℚ)^(-2:ℤ) : ℝ) = ((14891:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1745 : ((((452241070873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14897, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14891 < q → q < 14897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14897).mp (by decide +kernel))) hgap
  have hprev := s2L_1744
  have hrat : ((452241070873 : ℚ) / 1000000000000) ≤ ((452241066367 : ℚ) / 1000000000000) + (14897:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241070873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241066367 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14897:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14897:ℚ)^(-2:ℤ) : ℝ) = ((14897:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1746 : ((((452241075363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14897 < q → q < 14923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14923).mp (by decide +kernel))) hgap
  have hprev := s2L_1745
  have hrat : ((452241075363 : ℚ) / 1000000000000) ≤ ((452241070873 : ℚ) / 1000000000000) + (14923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241075363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241070873 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14923:ℚ)^(-2:ℤ) : ℝ) = ((14923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1747 : ((((452241079849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14923 < q → q < 14929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14929).mp (by decide +kernel))) hgap
  have hprev := s2L_1746
  have hrat : ((452241079849 : ℚ) / 1000000000000) ≤ ((452241075363 : ℚ) / 1000000000000) + (14929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241079849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241075363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14929:ℚ)^(-2:ℤ) : ℝ) = ((14929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1748 : ((((452241084329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14929 < q → q < 14939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14939).mp (by decide +kernel))) hgap
  have hprev := s2L_1747
  have hrat : ((452241084329 : ℚ) / 1000000000000) ≤ ((452241079849 : ℚ) / 1000000000000) + (14939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241084329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241079849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14939:ℚ)^(-2:ℤ) : ℝ) = ((14939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1749 : ((((90448217761 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14939 < q → q < 14947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14947).mp (by decide +kernel))) hgap
  have hprev := s2L_1748
  have hrat : ((90448217761 : ℚ) / 200000000000) ≤ ((452241084329 : ℚ) / 1000000000000) + (14947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448217761 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241084329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((14947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14947:ℚ)^(-2:ℤ) : ℝ) = ((14947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1750 : ((((226120546639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14947 < q → q < 14951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14951).mp (by decide +kernel))) hgap
  have hprev := s2L_1749
  have hrat : ((226120546639 : ℚ) / 500000000000) ≤ ((90448217761 : ℚ) / 200000000000) + (14951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120546639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448217761 : ℚ) / 200000000000) : ℚ) : ℝ) + ((14951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14951:ℚ)^(-2:ℤ) : ℝ) = ((14951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1751 : ((((113060274437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14951 < q → q < 14957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14957).mp (by decide +kernel))) hgap
  have hprev := s2L_1750
  have hrat : ((113060274437 : ℚ) / 250000000000) ≤ ((226120546639 : ℚ) / 500000000000) + (14957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060274437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120546639 : ℚ) / 500000000000) : ℚ) : ℝ) + ((14957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14957:ℚ)^(-2:ℤ) : ℝ) = ((14957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1752 : ((((45224110221 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14957 < q → q < 14969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14969).mp (by decide +kernel))) hgap
  have hprev := s2L_1751
  have hrat : ((45224110221 : ℚ) / 100000000000) ≤ ((113060274437 : ℚ) / 250000000000) + (14969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224110221 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060274437 : ℚ) / 250000000000) : ℚ) : ℝ) + ((14969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14969:ℚ)^(-2:ℤ) : ℝ) = ((14969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1753 : ((((56530138333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 14983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14969 < q → q < 14983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 14983).mp (by decide +kernel))) hgap
  have hprev := s2L_1752
  have hrat : ((56530138333 : ℚ) / 125000000000) ≤ ((45224110221 : ℚ) / 100000000000) + (14983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530138333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45224110221 : ℚ) / 100000000000) : ℚ) : ℝ) + ((14983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((14983:ℚ)^(-2:ℤ) : ℝ) = ((14983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1754 : ((((4522411111 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 14983 < q → q < 15013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15013).mp (by decide +kernel))) hgap
  have hprev := s2L_1753
  have hrat : ((4522411111 : ℚ) / 10000000000) ≤ ((56530138333 : ℚ) / 125000000000) + (15013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522411111 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((56530138333 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15013:ℚ)^(-2:ℤ) : ℝ) = ((15013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1755 : ((((226120557767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15013 < q → q < 15017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15017).mp (by decide +kernel))) hgap
  have hprev := s2L_1754
  have hrat : ((226120557767 : ℚ) / 500000000000) ≤ ((4522411111 : ℚ) / 10000000000) + (15017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120557767 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522411111 : ℚ) / 10000000000) : ℚ) : ℝ) + ((15017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15017:ℚ)^(-2:ℤ) : ℝ) = ((15017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1756 : ((((11306027999 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15017 < q → q < 15031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15031).mp (by decide +kernel))) hgap
  have hprev := s2L_1755
  have hrat : ((11306027999 : ℚ) / 25000000000) ≤ ((226120557767 : ℚ) / 500000000000) + (15031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306027999 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226120557767 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15031:ℚ)^(-2:ℤ) : ℝ) = ((15031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1757 : ((((452241124373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15031 < q → q < 15053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15053).mp (by decide +kernel))) hgap
  have hprev := s2L_1756
  have hrat : ((452241124373 : ℚ) / 1000000000000) ≤ ((11306027999 : ℚ) / 25000000000) + (15053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241124373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306027999 : ℚ) / 25000000000) : ℚ) : ℝ) + ((15053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15053:ℚ)^(-2:ℤ) : ℝ) = ((15053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1758 : ((((452241128781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15053 < q → q < 15061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15061).mp (by decide +kernel))) hgap
  have hprev := s2L_1757
  have hrat : ((452241128781 : ℚ) / 1000000000000) ≤ ((452241124373 : ℚ) / 1000000000000) + (15061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241128781 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241124373 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15061:ℚ)^(-2:ℤ) : ℝ) = ((15061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1759 : ((((226120566591 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15061 < q → q < 15073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15073).mp (by decide +kernel))) hgap
  have hprev := s2L_1758
  have hrat : ((226120566591 : ℚ) / 500000000000) ≤ ((452241128781 : ℚ) / 1000000000000) + (15073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120566591 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241128781 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15073:ℚ)^(-2:ℤ) : ℝ) = ((15073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1760 : ((((452241137581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15073 < q → q < 15077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15077).mp (by decide +kernel))) hgap
  have hprev := s2L_1759
  have hrat : ((452241137581 : ℚ) / 1000000000000) ≤ ((226120566591 : ℚ) / 500000000000) + (15077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241137581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120566591 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15077:ℚ)^(-2:ℤ) : ℝ) = ((15077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1761 : ((((56530142747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15077 < q → q < 15083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15083).mp (by decide +kernel))) hgap
  have hprev := s2L_1760
  have hrat : ((56530142747 : ℚ) / 125000000000) ≤ ((452241137581 : ℚ) / 1000000000000) + (15083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530142747 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452241137581 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15083:ℚ)^(-2:ℤ) : ℝ) = ((15083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1762 : ((((452241146367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15083 < q → q < 15091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15091).mp (by decide +kernel))) hgap
  have hprev := s2L_1761
  have hrat : ((452241146367 : ℚ) / 1000000000000) ≤ ((56530142747 : ℚ) / 125000000000) + (15091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241146367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530142747 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15091:ℚ)^(-2:ℤ) : ℝ) = ((15091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1763 : ((((14132535961 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15091 < q → q < 15101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15101).mp (by decide +kernel))) hgap
  have hprev := s2L_1762
  have hrat : ((14132535961 : ℚ) / 31250000000) ≤ ((452241146367 : ℚ) / 1000000000000) + (15101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132535961 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452241146367 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15101:ℚ)^(-2:ℤ) : ℝ) = ((15101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1764 : ((((452241155133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15101 < q → q < 15107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15107).mp (by decide +kernel))) hgap
  have hprev := s2L_1763
  have hrat : ((452241155133 : ℚ) / 1000000000000) ≤ ((14132535961 : ℚ) / 31250000000) + (15107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241155133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132535961 : ℚ) / 31250000000) : ℚ) : ℝ) + ((15107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15107:ℚ)^(-2:ℤ) : ℝ) = ((15107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1765 : ((((226120579753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15107 < q → q < 15121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15121).mp (by decide +kernel))) hgap
  have hprev := s2L_1764
  have hrat : ((226120579753 : ℚ) / 500000000000) ≤ ((452241155133 : ℚ) / 1000000000000) + (15121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120579753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241155133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15121:ℚ)^(-2:ℤ) : ℝ) = ((15121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1766 : ((((452241163873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15121 < q → q < 15131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15131).mp (by decide +kernel))) hgap
  have hprev := s2L_1765
  have hrat : ((452241163873 : ℚ) / 1000000000000) ≤ ((226120579753 : ℚ) / 500000000000) + (15131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241163873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120579753 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15131:ℚ)^(-2:ℤ) : ℝ) = ((15131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1767 : ((((452241168237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15131 < q → q < 15137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15137).mp (by decide +kernel))) hgap
  have hprev := s2L_1766
  have hrat : ((452241168237 : ℚ) / 1000000000000) ≤ ((452241163873 : ℚ) / 1000000000000) + (15137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241168237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241163873 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15137:ℚ)^(-2:ℤ) : ℝ) = ((15137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1768 : ((((2261205863 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15137 < q → q < 15139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15139).mp (by decide +kernel))) hgap
  have hprev := s2L_1767
  have hrat : ((2261205863 : ℚ) / 5000000000) ≤ ((452241168237 : ℚ) / 1000000000000) + (15139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261205863 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452241168237 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15139:ℚ)^(-2:ℤ) : ℝ) = ((15139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1769 : ((((452241176957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15139 < q → q < 15149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15149).mp (by decide +kernel))) hgap
  have hprev := s2L_1768
  have hrat : ((452241176957 : ℚ) / 1000000000000) ≤ ((2261205863 : ℚ) / 5000000000) + (15149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241176957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2261205863 : ℚ) / 5000000000) : ℚ) : ℝ) + ((15149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15149:ℚ)^(-2:ℤ) : ℝ) = ((15149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1770 : ((((452241181307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15149 < q → q < 15161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15161).mp (by decide +kernel))) hgap
  have hprev := s2L_1769
  have hrat : ((452241181307 : ℚ) / 1000000000000) ≤ ((452241176957 : ℚ) / 1000000000000) + (15161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241181307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241176957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15161:ℚ)^(-2:ℤ) : ℝ) = ((15161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1771 : ((((9044823713 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15161 < q → q < 15173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15173).mp (by decide +kernel))) hgap
  have hprev := s2L_1770
  have hrat : ((9044823713 : ℚ) / 20000000000) ≤ ((452241181307 : ℚ) / 1000000000000) + (15173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044823713 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452241181307 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15173:ℚ)^(-2:ℤ) : ℝ) = ((15173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1772 : ((((90448237997 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15173 < q → q < 15187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15187).mp (by decide +kernel))) hgap
  have hprev := s2L_1771
  have hrat : ((90448237997 : ℚ) / 200000000000) ≤ ((9044823713 : ℚ) / 20000000000) + (15187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448237997 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9044823713 : ℚ) / 20000000000) : ℚ) : ℝ) + ((15187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15187:ℚ)^(-2:ℤ) : ℝ) = ((15187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1773 : ((((452241194317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15187 < q → q < 15193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15193).mp (by decide +kernel))) hgap
  have hprev := s2L_1772
  have hrat : ((452241194317 : ℚ) / 1000000000000) ≤ ((90448237997 : ℚ) / 200000000000) + (15193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241194317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448237997 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15193:ℚ)^(-2:ℤ) : ℝ) = ((15193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1774 : ((((90448239729 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15199, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15193 < q → q < 15199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15199).mp (by decide +kernel))) hgap
  have hprev := s2L_1773
  have hrat : ((90448239729 : ℚ) / 200000000000) ≤ ((452241194317 : ℚ) / 1000000000000) + (15199:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448239729 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241194317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15199:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15199:ℚ)^(-2:ℤ) : ℝ) = ((15199:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1775 : ((((452241202963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15199 < q → q < 15217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15217).mp (by decide +kernel))) hgap
  have hprev := s2L_1774
  have hrat : ((452241202963 : ℚ) / 1000000000000) ≤ ((90448239729 : ℚ) / 200000000000) + (15217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241202963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448239729 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15217:ℚ)^(-2:ℤ) : ℝ) = ((15217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1776 : ((((18089648291 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15217 < q → q < 15227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15227).mp (by decide +kernel))) hgap
  have hprev := s2L_1775
  have hrat : ((18089648291 : ℚ) / 40000000000) ≤ ((452241202963 : ℚ) / 1000000000000) + (15227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089648291 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452241202963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15227:ℚ)^(-2:ℤ) : ℝ) = ((15227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1777 : ((((7066268931 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15227 < q → q < 15233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15233).mp (by decide +kernel))) hgap
  have hprev := s2L_1776
  have hrat : ((7066268931 : ℚ) / 15625000000) ≤ ((18089648291 : ℚ) / 40000000000) + (15233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066268931 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((18089648291 : ℚ) / 40000000000) : ℚ) : ℝ) + ((15233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15233:ℚ)^(-2:ℤ) : ℝ) = ((15233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1778 : ((((28265075993 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15233 < q → q < 15241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15241).mp (by decide +kernel))) hgap
  have hprev := s2L_1777
  have hrat : ((28265075993 : ℚ) / 62500000000) ≤ ((7066268931 : ℚ) / 15625000000) + (15241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265075993 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((7066268931 : ℚ) / 15625000000) : ℚ) : ℝ) + ((15241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15241:ℚ)^(-2:ℤ) : ℝ) = ((15241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1779 : ((((226120610091 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15241 < q → q < 15259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15259).mp (by decide +kernel))) hgap
  have hprev := s2L_1778
  have hrat : ((226120610091 : ℚ) / 500000000000) ≤ ((28265075993 : ℚ) / 62500000000) + (15259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120610091 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265075993 : ℚ) / 62500000000) : ℚ) : ℝ) + ((15259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15259:ℚ)^(-2:ℤ) : ℝ) = ((15259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1780 : ((((226120612237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15259 < q → q < 15263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15263).mp (by decide +kernel))) hgap
  have hprev := s2L_1779
  have hrat : ((226120612237 : ℚ) / 500000000000) ≤ ((226120610091 : ℚ) / 500000000000) + (15263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120612237 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120610091 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15263:ℚ)^(-2:ℤ) : ℝ) = ((15263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1781 : ((((452241228763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15263 < q → q < 15269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15269).mp (by decide +kernel))) hgap
  have hprev := s2L_1780
  have hrat : ((452241228763 : ℚ) / 1000000000000) ≤ ((226120612237 : ℚ) / 500000000000) + (15269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241228763 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120612237 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15269:ℚ)^(-2:ℤ) : ℝ) = ((15269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1782 : ((((452241233051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15269 < q → q < 15271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15271).mp (by decide +kernel))) hgap
  have hprev := s2L_1781
  have hrat : ((452241233051 : ℚ) / 1000000000000) ≤ ((452241228763 : ℚ) / 1000000000000) + (15271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241233051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241228763 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15271:ℚ)^(-2:ℤ) : ℝ) = ((15271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1783 : ((((90448247467 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15271 < q → q < 15277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15277).mp (by decide +kernel))) hgap
  have hprev := s2L_1782
  have hrat : ((90448247467 : ℚ) / 200000000000) ≤ ((452241233051 : ℚ) / 1000000000000) + (15277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448247467 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241233051 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15277:ℚ)^(-2:ℤ) : ℝ) = ((15277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1784 : ((((226120620807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15277 < q → q < 15287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15287).mp (by decide +kernel))) hgap
  have hprev := s2L_1783
  have hrat : ((226120620807 : ℚ) / 500000000000) ≤ ((90448247467 : ℚ) / 200000000000) + (15287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120620807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448247467 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15287:ℚ)^(-2:ℤ) : ℝ) = ((15287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1785 : ((((113060311473 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15287 < q → q < 15289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15289).mp (by decide +kernel))) hgap
  have hprev := s2L_1784
  have hrat : ((113060311473 : ℚ) / 250000000000) ≤ ((226120620807 : ℚ) / 500000000000) + (15289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060311473 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120620807 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15289:ℚ)^(-2:ℤ) : ℝ) = ((15289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1786 : ((((113060312541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15289 < q → q < 15299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15299).mp (by decide +kernel))) hgap
  have hprev := s2L_1785
  have hrat : ((113060312541 : ℚ) / 250000000000) ≤ ((113060311473 : ℚ) / 250000000000) + (15299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060312541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060311473 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15299:ℚ)^(-2:ℤ) : ℝ) = ((15299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1787 : ((((452241254431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15299 < q → q < 15307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15307).mp (by decide +kernel))) hgap
  have hprev := s2L_1786
  have hrat : ((452241254431 : ℚ) / 1000000000000) ≤ ((113060312541 : ℚ) / 250000000000) + (15307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241254431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060312541 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15307:ℚ)^(-2:ℤ) : ℝ) = ((15307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1788 : ((((90448251739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15307 < q → q < 15313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15313).mp (by decide +kernel))) hgap
  have hprev := s2L_1787
  have hrat : ((90448251739 : ℚ) / 200000000000) ≤ ((452241254431 : ℚ) / 1000000000000) + (15313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448251739 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241254431 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15313:ℚ)^(-2:ℤ) : ℝ) = ((15313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1789 : ((((113060315739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15313 < q → q < 15319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15319).mp (by decide +kernel))) hgap
  have hprev := s2L_1788
  have hrat : ((113060315739 : ℚ) / 250000000000) ≤ ((90448251739 : ℚ) / 200000000000) + (15319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060315739 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448251739 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15319:ℚ)^(-2:ℤ) : ℝ) = ((15319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1790 : ((((452241267211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15319 < q → q < 15329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15329).mp (by decide +kernel))) hgap
  have hprev := s2L_1789
  have hrat : ((452241267211 : ℚ) / 1000000000000) ≤ ((113060315739 : ℚ) / 250000000000) + (15329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241267211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060315739 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15329:ℚ)^(-2:ℤ) : ℝ) = ((15329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1791 : ((((90448254293 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15329 < q → q < 15331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15331).mp (by decide +kernel))) hgap
  have hprev := s2L_1790
  have hrat : ((90448254293 : ℚ) / 200000000000) ≤ ((452241267211 : ℚ) / 1000000000000) + (15331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448254293 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241267211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15331:ℚ)^(-2:ℤ) : ℝ) = ((15331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1792 : ((((452241275709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15331 < q → q < 15349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15349).mp (by decide +kernel))) hgap
  have hprev := s2L_1791
  have hrat : ((452241275709 : ℚ) / 1000000000000) ≤ ((90448254293 : ℚ) / 200000000000) + (15349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241275709 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448254293 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15349:ℚ)^(-2:ℤ) : ℝ) = ((15349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1793 : ((((113060319987 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15349 < q → q < 15359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15359).mp (by decide +kernel))) hgap
  have hprev := s2L_1792
  have hrat : ((113060319987 : ℚ) / 250000000000) ≤ ((452241275709 : ℚ) / 1000000000000) + (15359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060319987 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241275709 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15359:ℚ)^(-2:ℤ) : ℝ) = ((15359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1794 : ((((226120642093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15359 < q → q < 15361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15361).mp (by decide +kernel))) hgap
  have hprev := s2L_1793
  have hrat : ((226120642093 : ℚ) / 500000000000) ≤ ((113060319987 : ℚ) / 250000000000) + (15361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120642093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060319987 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15361:ℚ)^(-2:ℤ) : ℝ) = ((15361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1795 : ((((452241288417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15361 < q → q < 15373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15373).mp (by decide +kernel))) hgap
  have hprev := s2L_1794
  have hrat : ((452241288417 : ℚ) / 1000000000000) ≤ ((226120642093 : ℚ) / 500000000000) + (15373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241288417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120642093 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15373:ℚ)^(-2:ℤ) : ℝ) = ((15373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1796 : ((((226120646323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15373 < q → q < 15377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15377).mp (by decide +kernel))) hgap
  have hprev := s2L_1795
  have hrat : ((226120646323 : ℚ) / 500000000000) ≤ ((452241288417 : ℚ) / 1000000000000) + (15377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120646323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241288417 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15377:ℚ)^(-2:ℤ) : ℝ) = ((15377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1797 : ((((452241296871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15377 < q → q < 15383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15383).mp (by decide +kernel))) hgap
  have hprev := s2L_1796
  have hrat : ((452241296871 : ℚ) / 1000000000000) ≤ ((226120646323 : ℚ) / 500000000000) + (15383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241296871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120646323 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15383:ℚ)^(-2:ℤ) : ℝ) = ((15383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1798 : ((((113060325273 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15383 < q → q < 15391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15391).mp (by decide +kernel))) hgap
  have hprev := s2L_1797
  have hrat : ((113060325273 : ℚ) / 250000000000) ≤ ((452241296871 : ℚ) / 1000000000000) + (15391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060325273 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241296871 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15391:ℚ)^(-2:ℤ) : ℝ) = ((15391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1799 : ((((113060326327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15391 < q → q < 15401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15401).mp (by decide +kernel))) hgap
  have hprev := s2L_1798
  have hrat : ((113060326327 : ℚ) / 250000000000) ≤ ((113060325273 : ℚ) / 250000000000) + (15401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060326327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060325273 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15401:ℚ)^(-2:ℤ) : ℝ) = ((15401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1800 : ((((452241309517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15401 < q → q < 15413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15413).mp (by decide +kernel))) hgap
  have hprev := s2L_1799
  have hrat : ((452241309517 : ℚ) / 1000000000000) ≤ ((113060326327 : ℚ) / 250000000000) + (15413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241309517 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060326327 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15413:ℚ)^(-2:ℤ) : ℝ) = ((15413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1801 : ((((226120656859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15413 < q → q < 15427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15427).mp (by decide +kernel))) hgap
  have hprev := s2L_1800
  have hrat : ((226120656859 : ℚ) / 500000000000) ≤ ((452241309517 : ℚ) / 1000000000000) + (15427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120656859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241309517 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15427:ℚ)^(-2:ℤ) : ℝ) = ((15427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1802 : ((((452241317913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15427 < q → q < 15439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15439).mp (by decide +kernel))) hgap
  have hprev := s2L_1801
  have hrat : ((452241317913 : ℚ) / 1000000000000) ≤ ((226120656859 : ℚ) / 500000000000) + (15439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241317913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120656859 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15439:ℚ)^(-2:ℤ) : ℝ) = ((15439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1803 : ((((226120661053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15439 < q → q < 15443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15443).mp (by decide +kernel))) hgap
  have hprev := s2L_1802
  have hrat : ((226120661053 : ℚ) / 500000000000) ≤ ((452241317913 : ℚ) / 1000000000000) + (15443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120661053 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241317913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15443:ℚ)^(-2:ℤ) : ℝ) = ((15443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1804 : ((((226120663147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15443 < q → q < 15451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15451).mp (by decide +kernel))) hgap
  have hprev := s2L_1803
  have hrat : ((226120663147 : ℚ) / 500000000000) ≤ ((226120661053 : ℚ) / 500000000000) + (15451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120663147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120661053 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15451:ℚ)^(-2:ℤ) : ℝ) = ((15451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1805 : ((((452241330477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15451 < q → q < 15461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15461).mp (by decide +kernel))) hgap
  have hprev := s2L_1804
  have hrat : ((452241330477 : ℚ) / 1000000000000) ≤ ((226120663147 : ℚ) / 500000000000) + (15461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241330477 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120663147 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15461:ℚ)^(-2:ℤ) : ℝ) = ((15461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1806 : ((((452241334657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15461 < q → q < 15467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15467).mp (by decide +kernel))) hgap
  have hprev := s2L_1805
  have hrat : ((452241334657 : ℚ) / 1000000000000) ≤ ((452241330477 : ℚ) / 1000000000000) + (15467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241334657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241330477 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15467:ℚ)^(-2:ℤ) : ℝ) = ((15467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1807 : ((((452241338833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15467 < q → q < 15473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15473).mp (by decide +kernel))) hgap
  have hprev := s2L_1806
  have hrat : ((452241338833 : ℚ) / 1000000000000) ≤ ((452241334657 : ℚ) / 1000000000000) + (15473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241338833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241334657 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15473:ℚ)^(-2:ℤ) : ℝ) = ((15473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1808 : ((((452241342999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15473 < q → q < 15493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15493).mp (by decide +kernel))) hgap
  have hprev := s2L_1807
  have hrat : ((452241342999 : ℚ) / 1000000000000) ≤ ((452241338833 : ℚ) / 1000000000000) + (15493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241342999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241338833 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15493:ℚ)^(-2:ℤ) : ℝ) = ((15493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1809 : ((((226120673581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15493 < q → q < 15497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15497).mp (by decide +kernel))) hgap
  have hprev := s2L_1808
  have hrat : ((226120673581 : ℚ) / 500000000000) ≤ ((452241342999 : ℚ) / 1000000000000) + (15497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120673581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241342999 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15497:ℚ)^(-2:ℤ) : ℝ) = ((15497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1810 : ((((226120675659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15497 < q → q < 15511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15511).mp (by decide +kernel))) hgap
  have hprev := s2L_1809
  have hrat : ((226120675659 : ℚ) / 500000000000) ≤ ((226120673581 : ℚ) / 500000000000) + (15511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120675659 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120673581 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15511:ℚ)^(-2:ℤ) : ℝ) = ((15511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1811 : ((((90448271093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15511 < q → q < 15527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15527).mp (by decide +kernel))) hgap
  have hprev := s2L_1810
  have hrat : ((90448271093 : ℚ) / 200000000000) ≤ ((226120675659 : ℚ) / 500000000000) + (15527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448271093 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226120675659 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15527:ℚ)^(-2:ℤ) : ℝ) = ((15527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1812 : ((((90448271921 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15527 < q → q < 15541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15541).mp (by decide +kernel))) hgap
  have hprev := s2L_1811
  have hrat : ((90448271921 : ℚ) / 200000000000) ≤ ((90448271093 : ℚ) / 200000000000) + (15541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448271921 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448271093 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15541:ℚ)^(-2:ℤ) : ℝ) = ((15541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1813 : ((((22612068187 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15541 < q → q < 15551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15551).mp (by decide +kernel))) hgap
  have hprev := s2L_1812
  have hrat : ((22612068187 : ℚ) / 50000000000) ≤ ((90448271921 : ℚ) / 200000000000) + (15551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612068187 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((90448271921 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15551:ℚ)^(-2:ℤ) : ℝ) = ((15551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1814 : ((((45224136787 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15551 < q → q < 15559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15559).mp (by decide +kernel))) hgap
  have hprev := s2L_1813
  have hrat : ((45224136787 : ℚ) / 100000000000) ≤ ((22612068187 : ℚ) / 50000000000) + (15559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224136787 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22612068187 : ℚ) / 50000000000) : ℚ) : ℝ) + ((15559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15559:ℚ)^(-2:ℤ) : ℝ) = ((15559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1815 : ((((90448274399 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15559 < q → q < 15569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15569).mp (by decide +kernel))) hgap
  have hprev := s2L_1814
  have hrat : ((90448274399 : ℚ) / 200000000000) ≤ ((45224136787 : ℚ) / 100000000000) + (15569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448274399 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45224136787 : ℚ) / 100000000000) : ℚ) : ℝ) + ((15569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15569:ℚ)^(-2:ℤ) : ℝ) = ((15569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1816 : ((((226120688057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15569 < q → q < 15581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15581).mp (by decide +kernel))) hgap
  have hprev := s2L_1815
  have hrat : ((226120688057 : ℚ) / 500000000000) ≤ ((90448274399 : ℚ) / 200000000000) + (15581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120688057 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448274399 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15581:ℚ)^(-2:ℤ) : ℝ) = ((15581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1817 : ((((56530172529 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15581 < q → q < 15583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15583).mp (by decide +kernel))) hgap
  have hprev := s2L_1816
  have hrat : ((56530172529 : ℚ) / 125000000000) ≤ ((226120688057 : ℚ) / 500000000000) + (15583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530172529 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226120688057 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15583:ℚ)^(-2:ℤ) : ℝ) = ((15583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1818 : ((((22612069217 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15583 < q → q < 15601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15601).mp (by decide +kernel))) hgap
  have hprev := s2L_1817
  have hrat : ((22612069217 : ℚ) / 50000000000) ≤ ((56530172529 : ℚ) / 125000000000) + (15601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612069217 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56530172529 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15601:ℚ)^(-2:ℤ) : ℝ) = ((15601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1819 : ((((90448277689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15601 < q → q < 15607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15607).mp (by decide +kernel))) hgap
  have hprev := s2L_1818
  have hrat : ((90448277689 : ℚ) / 200000000000) ≤ ((22612069217 : ℚ) / 50000000000) + (15607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448277689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612069217 : ℚ) / 50000000000) : ℚ) : ℝ) + ((15607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15607:ℚ)^(-2:ℤ) : ℝ) = ((15607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1820 : ((((14132543517 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15607 < q → q < 15619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15619).mp (by decide +kernel))) hgap
  have hprev := s2L_1819
  have hrat : ((14132543517 : ℚ) / 31250000000) ≤ ((90448277689 : ℚ) / 200000000000) + (15619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132543517 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((90448277689 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15619:ℚ)^(-2:ℤ) : ℝ) = ((15619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1821 : ((((452241396637 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15619 < q → q < 15629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15629).mp (by decide +kernel))) hgap
  have hprev := s2L_1820
  have hrat : ((452241396637 : ℚ) / 1000000000000) ≤ ((14132543517 : ℚ) / 31250000000) + (15629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241396637 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132543517 : ℚ) / 31250000000) : ℚ) : ℝ) + ((15629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15629:ℚ)^(-2:ℤ) : ℝ) = ((15629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1822 : ((((113060350181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15629 < q → q < 15641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15641).mp (by decide +kernel))) hgap
  have hprev := s2L_1821
  have hrat : ((113060350181 : ℚ) / 250000000000) ≤ ((452241396637 : ℚ) / 1000000000000) + (15641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060350181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241396637 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15641:ℚ)^(-2:ℤ) : ℝ) = ((15641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1823 : ((((45224140481 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15641 < q → q < 15643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15643).mp (by decide +kernel))) hgap
  have hprev := s2L_1822
  have hrat : ((45224140481 : ℚ) / 100000000000) ≤ ((113060350181 : ℚ) / 250000000000) + (15643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224140481 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060350181 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15643:ℚ)^(-2:ℤ) : ℝ) = ((15643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1824 : ((((226120704447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15643 < q → q < 15647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15647).mp (by decide +kernel))) hgap
  have hprev := s2L_1823
  have hrat : ((226120704447 : ℚ) / 500000000000) ≤ ((45224140481 : ℚ) / 100000000000) + (15647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120704447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224140481 : ℚ) / 100000000000) : ℚ) : ℝ) + ((15647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15647:ℚ)^(-2:ℤ) : ℝ) = ((15647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1825 : ((((452241412977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15647 < q → q < 15649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15649).mp (by decide +kernel))) hgap
  have hprev := s2L_1824
  have hrat : ((452241412977 : ℚ) / 1000000000000) ≤ ((226120704447 : ℚ) / 500000000000) + (15649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241412977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120704447 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15649:ℚ)^(-2:ℤ) : ℝ) = ((15649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1826 : ((((226120708527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15649 < q → q < 15661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15661).mp (by decide +kernel))) hgap
  have hprev := s2L_1825
  have hrat : ((226120708527 : ℚ) / 500000000000) ≤ ((452241412977 : ℚ) / 1000000000000) + (15661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120708527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241412977 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15661:ℚ)^(-2:ℤ) : ℝ) = ((15661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1827 : ((((56530177641 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15667, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15661 < q → q < 15667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15667).mp (by decide +kernel))) hgap
  have hprev := s2L_1826
  have hrat : ((56530177641 : ℚ) / 125000000000) ≤ ((226120708527 : ℚ) / 500000000000) + (15667:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530177641 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226120708527 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15667:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15667:ℚ)^(-2:ℤ) : ℝ) = ((15667:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1828 : ((((452241425199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15667 < q → q < 15671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15671).mp (by decide +kernel))) hgap
  have hprev := s2L_1827
  have hrat : ((452241425199 : ℚ) / 1000000000000) ≤ ((56530177641 : ℚ) / 125000000000) + (15671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241425199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530177641 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15671:ℚ)^(-2:ℤ) : ℝ) = ((15671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1829 : ((((226120714633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15671 < q → q < 15679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15679).mp (by decide +kernel))) hgap
  have hprev := s2L_1828
  have hrat : ((226120714633 : ℚ) / 500000000000) ≤ ((452241425199 : ℚ) / 1000000000000) + (15679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120714633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241425199 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15679:ℚ)^(-2:ℤ) : ℝ) = ((15679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1830 : ((((452241433331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15679 < q → q < 15683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15683).mp (by decide +kernel))) hgap
  have hprev := s2L_1829
  have hrat : ((452241433331 : ℚ) / 1000000000000) ≤ ((226120714633 : ℚ) / 500000000000) + (15683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241433331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120714633 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15683:ℚ)^(-2:ℤ) : ℝ) = ((15683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1831 : ((((226120718687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15683 < q → q < 15727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15727).mp (by decide +kernel))) hgap
  have hprev := s2L_1830
  have hrat : ((226120718687 : ℚ) / 500000000000) ≤ ((452241433331 : ℚ) / 1000000000000) + (15727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120718687 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241433331 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15727:ℚ)^(-2:ℤ) : ℝ) = ((15727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1832 : ((((226120720707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15727 < q → q < 15731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15731).mp (by decide +kernel))) hgap
  have hprev := s2L_1831
  have hrat : ((226120720707 : ℚ) / 500000000000) ≤ ((226120718687 : ℚ) / 500000000000) + (15731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120720707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120718687 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15731:ℚ)^(-2:ℤ) : ℝ) = ((15731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1833 : ((((452241445453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15731 < q → q < 15733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15733).mp (by decide +kernel))) hgap
  have hprev := s2L_1832
  have hrat : ((452241445453 : ℚ) / 1000000000000) ≤ ((226120720707 : ℚ) / 500000000000) + (15733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241445453 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120720707 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15733:ℚ)^(-2:ℤ) : ℝ) = ((15733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1834 : ((((45224144949 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15733 < q → q < 15737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15737).mp (by decide +kernel))) hgap
  have hprev := s2L_1833
  have hrat : ((45224144949 : ℚ) / 100000000000) ≤ ((452241445453 : ℚ) / 1000000000000) + (15737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224144949 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452241445453 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15737:ℚ)^(-2:ℤ) : ℝ) = ((15737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1835 : ((((226120726763 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15737 < q → q < 15739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15739).mp (by decide +kernel))) hgap
  have hprev := s2L_1834
  have hrat : ((226120726763 : ℚ) / 500000000000) ≤ ((45224144949 : ℚ) / 100000000000) + (15739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120726763 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224144949 : ℚ) / 100000000000) : ℚ) : ℝ) + ((15739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15739:ℚ)^(-2:ℤ) : ℝ) = ((15739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1836 : ((((452241457557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15739 < q → q < 15749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15749).mp (by decide +kernel))) hgap
  have hprev := s2L_1835
  have hrat : ((452241457557 : ℚ) / 1000000000000) ≤ ((226120726763 : ℚ) / 500000000000) + (15749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241457557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120726763 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15749:ℚ)^(-2:ℤ) : ℝ) = ((15749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1837 : ((((226120730791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15749 < q → q < 15761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15761).mp (by decide +kernel))) hgap
  have hprev := s2L_1836
  have hrat : ((226120730791 : ℚ) / 500000000000) ≤ ((452241457557 : ℚ) / 1000000000000) + (15761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120730791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241457557 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15761:ℚ)^(-2:ℤ) : ℝ) = ((15761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1838 : ((((113060366401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15761 < q → q < 15767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15767).mp (by decide +kernel))) hgap
  have hprev := s2L_1837
  have hrat : ((113060366401 : ℚ) / 250000000000) ≤ ((226120730791 : ℚ) / 500000000000) + (15767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060366401 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120730791 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15767:ℚ)^(-2:ℤ) : ℝ) = ((15767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1839 : ((((452241469623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15767 < q → q < 15773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15773).mp (by decide +kernel))) hgap
  have hprev := s2L_1838
  have hrat : ((452241469623 : ℚ) / 1000000000000) ≤ ((113060366401 : ℚ) / 250000000000) + (15773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241469623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060366401 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15773:ℚ)^(-2:ℤ) : ℝ) = ((15773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1840 : ((((90448294727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15773 < q → q < 15787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15787).mp (by decide +kernel))) hgap
  have hprev := s2L_1839
  have hrat : ((90448294727 : ℚ) / 200000000000) ≤ ((452241469623 : ℚ) / 1000000000000) + (15787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448294727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241469623 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15787:ℚ)^(-2:ℤ) : ℝ) = ((15787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1841 : ((((90448295529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15787 < q → q < 15791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15791).mp (by decide +kernel))) hgap
  have hprev := s2L_1840
  have hrat : ((90448295529 : ℚ) / 200000000000) ≤ ((90448294727 : ℚ) / 200000000000) + (15791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448295529 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448294727 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15791:ℚ)^(-2:ℤ) : ℝ) = ((15791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1842 : ((((113060370413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15791 < q → q < 15797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15797).mp (by decide +kernel))) hgap
  have hprev := s2L_1841
  have hrat : ((113060370413 : ℚ) / 250000000000) ≤ ((90448295529 : ℚ) / 200000000000) + (15797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060370413 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448295529 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15797:ℚ)^(-2:ℤ) : ℝ) = ((15797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1843 : ((((56530185707 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15797 < q → q < 15803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15803).mp (by decide +kernel))) hgap
  have hprev := s2L_1842
  have hrat : ((56530185707 : ℚ) / 125000000000) ≤ ((113060370413 : ℚ) / 250000000000) + (15803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530185707 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060370413 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15803:ℚ)^(-2:ℤ) : ℝ) = ((15803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1844 : ((((452241489657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15803 < q → q < 15809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15809).mp (by decide +kernel))) hgap
  have hprev := s2L_1843
  have hrat : ((452241489657 : ℚ) / 1000000000000) ≤ ((56530185707 : ℚ) / 125000000000) + (15809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241489657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530185707 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15809:ℚ)^(-2:ℤ) : ℝ) = ((15809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1845 : ((((226120746827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15809 < q → q < 15817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15817).mp (by decide +kernel))) hgap
  have hprev := s2L_1844
  have hrat : ((226120746827 : ℚ) / 500000000000) ≤ ((452241489657 : ℚ) / 1000000000000) + (15817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120746827 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241489657 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15817:ℚ)^(-2:ℤ) : ℝ) = ((15817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1846 : ((((28265093603 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15817 < q → q < 15823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15823).mp (by decide +kernel))) hgap
  have hprev := s2L_1845
  have hrat : ((28265093603 : ℚ) / 62500000000) ≤ ((226120746827 : ℚ) / 500000000000) + (15823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265093603 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226120746827 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15823:ℚ)^(-2:ℤ) : ℝ) = ((15823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1847 : ((((56530187703 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15823 < q → q < 15859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15859).mp (by decide +kernel))) hgap
  have hprev := s2L_1846
  have hrat : ((56530187703 : ℚ) / 125000000000) ≤ ((28265093603 : ℚ) / 62500000000) + (15859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530187703 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28265093603 : ℚ) / 62500000000) : ℚ) : ℝ) + ((15859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15859:ℚ)^(-2:ℤ) : ℝ) = ((15859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1848 : ((((452241505591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15859 < q → q < 15877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15877).mp (by decide +kernel))) hgap
  have hprev := s2L_1847
  have hrat : ((452241505591 : ℚ) / 1000000000000) ≤ ((56530187703 : ℚ) / 125000000000) + (15877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241505591 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530187703 : ℚ) / 125000000000) : ℚ) : ℝ) + ((15877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15877:ℚ)^(-2:ℤ) : ℝ) = ((15877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1849 : ((((113060377389 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15877 < q → q < 15881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15881).mp (by decide +kernel))) hgap
  have hprev := s2L_1848
  have hrat : ((113060377389 : ℚ) / 250000000000) ≤ ((452241505591 : ℚ) / 1000000000000) + (15881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060377389 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241505591 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15881:ℚ)^(-2:ℤ) : ℝ) = ((15881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1850 : ((((226120756759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15881 < q → q < 15887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15887).mp (by decide +kernel))) hgap
  have hprev := s2L_1849
  have hrat : ((226120756759 : ℚ) / 500000000000) ≤ ((113060377389 : ℚ) / 250000000000) + (15887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120756759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060377389 : ℚ) / 250000000000) : ℚ) : ℝ) + ((15887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15887:ℚ)^(-2:ℤ) : ℝ) = ((15887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1851 : ((((452241517479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15887 < q → q < 15889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15889).mp (by decide +kernel))) hgap
  have hprev := s2L_1850
  have hrat : ((452241517479 : ℚ) / 1000000000000) ≤ ((226120756759 : ℚ) / 500000000000) + (15889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241517479 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120756759 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15889:ℚ)^(-2:ℤ) : ℝ) = ((15889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1852 : ((((226120760717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15889 < q → q < 15901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15901).mp (by decide +kernel))) hgap
  have hprev := s2L_1851
  have hrat : ((226120760717 : ℚ) / 500000000000) ≤ ((452241517479 : ℚ) / 1000000000000) + (15901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120760717 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241517479 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15901:ℚ)^(-2:ℤ) : ℝ) = ((15901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1853 : ((((226120762693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15901 < q → q < 15907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15907).mp (by decide +kernel))) hgap
  have hprev := s2L_1852
  have hrat : ((226120762693 : ℚ) / 500000000000) ≤ ((226120760717 : ℚ) / 500000000000) + (15907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120762693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120760717 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15907:ℚ)^(-2:ℤ) : ℝ) = ((15907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1854 : ((((90448305867 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15907 < q → q < 15913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15913).mp (by decide +kernel))) hgap
  have hprev := s2L_1853
  have hrat : ((90448305867 : ℚ) / 200000000000) ≤ ((226120762693 : ℚ) / 500000000000) + (15913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448305867 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226120762693 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15913:ℚ)^(-2:ℤ) : ℝ) = ((15913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1855 : ((((452241533281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15913 < q → q < 15919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15919).mp (by decide +kernel))) hgap
  have hprev := s2L_1854
  have hrat : ((452241533281 : ℚ) / 1000000000000) ≤ ((90448305867 : ℚ) / 200000000000) + (15919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241533281 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448305867 : ℚ) / 200000000000) : ℚ) : ℝ) + ((15919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15919:ℚ)^(-2:ℤ) : ℝ) = ((15919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1856 : ((((18089661489 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15919 < q → q < 15923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15923).mp (by decide +kernel))) hgap
  have hprev := s2L_1855
  have hrat : ((18089661489 : ℚ) / 40000000000) ≤ ((452241533281 : ℚ) / 1000000000000) + (15923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089661489 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452241533281 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15923:ℚ)^(-2:ℤ) : ℝ) = ((15923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1857 : ((((226120770581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15923 < q → q < 15937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15937).mp (by decide +kernel))) hgap
  have hprev := s2L_1856
  have hrat : ((226120770581 : ℚ) / 500000000000) ≤ ((18089661489 : ℚ) / 40000000000) + (15937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120770581 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089661489 : ℚ) / 40000000000) : ℚ) : ℝ) + ((15937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15937:ℚ)^(-2:ℤ) : ℝ) = ((15937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1858 : ((((3533137071 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15937 < q → q < 15959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15959).mp (by decide +kernel))) hgap
  have hprev := s2L_1857
  have hrat : ((3533137071 : ℚ) / 7812500000) ≤ ((226120770581 : ℚ) / 500000000000) + (15959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533137071 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((226120770581 : ℚ) / 500000000000) : ℚ) : ℝ) + ((15959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15959:ℚ)^(-2:ℤ) : ℝ) = ((15959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1859 : ((((28265096813 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15959 < q → q < 15971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15971).mp (by decide +kernel))) hgap
  have hprev := s2L_1858
  have hrat : ((28265096813 : ℚ) / 62500000000) ≤ ((3533137071 : ℚ) / 7812500000) + (15971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265096813 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((3533137071 : ℚ) / 7812500000) : ℚ) : ℝ) + ((15971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15971:ℚ)^(-2:ℤ) : ℝ) = ((15971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1860 : ((((452241552927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15971 < q → q < 15973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15973).mp (by decide +kernel))) hgap
  have hprev := s2L_1859
  have hrat : ((452241552927 : ℚ) / 1000000000000) ≤ ((28265096813 : ℚ) / 62500000000) + (15973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241552927 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265096813 : ℚ) / 62500000000) : ℚ) : ℝ) + ((15973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15973:ℚ)^(-2:ℤ) : ℝ) = ((15973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1861 : ((((452241556837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 15991, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15973 < q → q < 15991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 15991).mp (by decide +kernel))) hgap
  have hprev := s2L_1860
  have hrat : ((452241556837 : ℚ) / 1000000000000) ≤ ((452241552927 : ℚ) / 1000000000000) + (15991:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241556837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241552927 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((15991:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((15991:ℚ)^(-2:ℤ) : ℝ) = ((15991:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1862 : ((((226120780371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 15991 < q → q < 16001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16001).mp (by decide +kernel))) hgap
  have hprev := s2L_1861
  have hrat : ((226120780371 : ℚ) / 500000000000) ≤ ((452241556837 : ℚ) / 1000000000000) + (16001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120780371 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241556837 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16001:ℚ)^(-2:ℤ) : ℝ) = ((16001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1863 : ((((113060391161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16001 < q → q < 16007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16007).mp (by decide +kernel))) hgap
  have hprev := s2L_1862
  have hrat : ((113060391161 : ℚ) / 250000000000) ≤ ((226120780371 : ℚ) / 500000000000) + (16007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060391161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120780371 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16007:ℚ)^(-2:ℤ) : ℝ) = ((16007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1864 : ((((226120784267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16007 < q → q < 16033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16033).mp (by decide +kernel))) hgap
  have hprev := s2L_1863
  have hrat : ((226120784267 : ℚ) / 500000000000) ≤ ((113060391161 : ℚ) / 250000000000) + (16033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120784267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060391161 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16033:ℚ)^(-2:ℤ) : ℝ) = ((16033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1865 : ((((113060393103 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16033 < q → q < 16057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16057).mp (by decide +kernel))) hgap
  have hprev := s2L_1864
  have hrat : ((113060393103 : ℚ) / 250000000000) ≤ ((226120784267 : ℚ) / 500000000000) + (16057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060393103 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120784267 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16057:ℚ)^(-2:ℤ) : ℝ) = ((16057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1866 : ((((14132549259 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16057 < q → q < 16061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16061).mp (by decide +kernel))) hgap
  have hprev := s2L_1865
  have hrat : ((14132549259 : ℚ) / 31250000000) ≤ ((113060393103 : ℚ) / 250000000000) + (16061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132549259 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113060393103 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16061:ℚ)^(-2:ℤ) : ℝ) = ((16061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1867 : ((((452241580163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16061 < q → q < 16063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16063).mp (by decide +kernel))) hgap
  have hprev := s2L_1866
  have hrat : ((452241580163 : ℚ) / 1000000000000) ≤ ((14132549259 : ℚ) / 31250000000) + (16063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241580163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132549259 : ℚ) / 31250000000) : ℚ) : ℝ) + ((16063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16063:ℚ)^(-2:ℤ) : ℝ) = ((16063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1868 : ((((113060396009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16063 < q → q < 16067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16067).mp (by decide +kernel))) hgap
  have hprev := s2L_1867
  have hrat : ((113060396009 : ℚ) / 250000000000) ≤ ((452241580163 : ℚ) / 1000000000000) + (16067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060396009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241580163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16067:ℚ)^(-2:ℤ) : ℝ) = ((16067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1869 : ((((113060396977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16067 < q → q < 16069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16069).mp (by decide +kernel))) hgap
  have hprev := s2L_1868
  have hrat : ((113060396977 : ℚ) / 250000000000) ≤ ((113060396009 : ℚ) / 250000000000) + (16069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060396977 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060396009 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16069:ℚ)^(-2:ℤ) : ℝ) = ((16069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1870 : ((((226120795889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16069 < q → q < 16073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16073).mp (by decide +kernel))) hgap
  have hprev := s2L_1869
  have hrat : ((226120795889 : ℚ) / 500000000000) ≤ ((113060396977 : ℚ) / 250000000000) + (16073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120795889 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060396977 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16073:ℚ)^(-2:ℤ) : ℝ) = ((16073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1871 : ((((226120797821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16073 < q → q < 16087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16087).mp (by decide +kernel))) hgap
  have hprev := s2L_1870
  have hrat : ((226120797821 : ℚ) / 500000000000) ≤ ((226120795889 : ℚ) / 500000000000) + (16087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120797821 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120795889 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16087:ℚ)^(-2:ℤ) : ℝ) = ((16087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1872 : ((((28265099969 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16087 < q → q < 16091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16091).mp (by decide +kernel))) hgap
  have hprev := s2L_1871
  have hrat : ((28265099969 : ℚ) / 62500000000) ≤ ((226120797821 : ℚ) / 500000000000) + (16091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265099969 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226120797821 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16091:ℚ)^(-2:ℤ) : ℝ) = ((16091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1873 : ((((452241603363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16091 < q → q < 16097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16097).mp (by decide +kernel))) hgap
  have hprev := s2L_1872
  have hrat : ((452241603363 : ℚ) / 1000000000000) ≤ ((28265099969 : ℚ) / 62500000000) + (16097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241603363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265099969 : ℚ) / 62500000000) : ℚ) : ℝ) + ((16097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16097:ℚ)^(-2:ℤ) : ℝ) = ((16097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1874 : ((((452241607219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16097 < q → q < 16103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16103).mp (by decide +kernel))) hgap
  have hprev := s2L_1873
  have hrat : ((452241607219 : ℚ) / 1000000000000) ≤ ((452241603363 : ℚ) / 1000000000000) + (16103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241607219 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241603363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16103:ℚ)^(-2:ℤ) : ℝ) = ((16103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1875 : ((((452241611071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16103 < q → q < 16111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16111).mp (by decide +kernel))) hgap
  have hprev := s2L_1874
  have hrat : ((452241611071 : ℚ) / 1000000000000) ≤ ((452241607219 : ℚ) / 1000000000000) + (16111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241611071 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241607219 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16111:ℚ)^(-2:ℤ) : ℝ) = ((16111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1876 : ((((90448322983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16111 < q → q < 16127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16127).mp (by decide +kernel))) hgap
  have hprev := s2L_1875
  have hrat : ((90448322983 : ℚ) / 200000000000) ≤ ((452241611071 : ℚ) / 1000000000000) + (16127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448322983 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241611071 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16127:ℚ)^(-2:ℤ) : ℝ) = ((16127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1877 : ((((226120809377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16127 < q → q < 16139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16139).mp (by decide +kernel))) hgap
  have hprev := s2L_1876
  have hrat : ((226120809377 : ℚ) / 500000000000) ≤ ((90448322983 : ℚ) / 200000000000) + (16139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120809377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448322983 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16139:ℚ)^(-2:ℤ) : ℝ) = ((16139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1878 : ((((7066275353 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16141, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16139 < q → q < 16141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16141).mp (by decide +kernel))) hgap
  have hprev := s2L_1877
  have hrat : ((7066275353 : ℚ) / 15625000000) ≤ ((226120809377 : ℚ) / 500000000000) + (16141:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066275353 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((226120809377 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16141:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16141:ℚ)^(-2:ℤ) : ℝ) = ((16141:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1879 : ((((45224162641 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16141 < q → q < 16183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16183).mp (by decide +kernel))) hgap
  have hprev := s2L_1878
  have hrat : ((45224162641 : ℚ) / 100000000000) ≤ ((7066275353 : ℚ) / 15625000000) + (16183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224162641 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((7066275353 : ℚ) / 15625000000) : ℚ) : ℝ) + ((16183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16183:ℚ)^(-2:ℤ) : ℝ) = ((16183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1880 : ((((226120815113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16183 < q → q < 16187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16187).mp (by decide +kernel))) hgap
  have hprev := s2L_1879
  have hrat : ((226120815113 : ℚ) / 500000000000) ≤ ((45224162641 : ℚ) / 100000000000) + (16187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120815113 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224162641 : ℚ) / 100000000000) : ℚ) : ℝ) + ((16187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16187:ℚ)^(-2:ℤ) : ℝ) = ((16187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1881 : ((((452241634041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16187 < q → q < 16189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16189).mp (by decide +kernel))) hgap
  have hprev := s2L_1880
  have hrat : ((452241634041 : ℚ) / 1000000000000) ≤ ((226120815113 : ℚ) / 500000000000) + (16189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241634041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120815113 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16189:ℚ)^(-2:ℤ) : ℝ) = ((16189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1882 : ((((226120818927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16189 < q → q < 16193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16193).mp (by decide +kernel))) hgap
  have hprev := s2L_1881
  have hrat : ((226120818927 : ℚ) / 500000000000) ≤ ((452241634041 : ℚ) / 1000000000000) + (16193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120818927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241634041 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16193:ℚ)^(-2:ℤ) : ℝ) = ((16193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1883 : ((((56530205207 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16193 < q → q < 16217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16217).mp (by decide +kernel))) hgap
  have hprev := s2L_1882
  have hrat : ((56530205207 : ℚ) / 125000000000) ≤ ((226120818927 : ℚ) / 500000000000) + (16217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530205207 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226120818927 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16217:ℚ)^(-2:ℤ) : ℝ) = ((16217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1884 : ((((90448329091 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16217 < q → q < 16223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16223).mp (by decide +kernel))) hgap
  have hprev := s2L_1883
  have hrat : ((90448329091 : ℚ) / 200000000000) ≤ ((56530205207 : ℚ) / 125000000000) + (16223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448329091 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530205207 : ℚ) / 125000000000) : ℚ) : ℝ) + ((16223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16223:ℚ)^(-2:ℤ) : ℝ) = ((16223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1885 : ((((452241649251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16223 < q → q < 16229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16229).mp (by decide +kernel))) hgap
  have hprev := s2L_1884
  have hrat : ((452241649251 : ℚ) / 1000000000000) ≤ ((90448329091 : ℚ) / 200000000000) + (16229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241649251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448329091 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16229:ℚ)^(-2:ℤ) : ℝ) = ((16229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1886 : ((((226120826523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16229 < q → q < 16231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16231).mp (by decide +kernel))) hgap
  have hprev := s2L_1885
  have hrat : ((226120826523 : ℚ) / 500000000000) ≤ ((452241649251 : ℚ) / 1000000000000) + (16231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120826523 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241649251 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16231:ℚ)^(-2:ℤ) : ℝ) = ((16231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1887 : ((((452241656833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16231 < q → q < 16249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16249).mp (by decide +kernel))) hgap
  have hprev := s2L_1886
  have hrat : ((452241656833 : ℚ) / 1000000000000) ≤ ((226120826523 : ℚ) / 500000000000) + (16249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241656833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120826523 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16249:ℚ)^(-2:ℤ) : ℝ) = ((16249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1888 : ((((226120830309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16249 < q → q < 16253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16253).mp (by decide +kernel))) hgap
  have hprev := s2L_1887
  have hrat : ((226120830309 : ℚ) / 500000000000) ≤ ((452241656833 : ℚ) / 1000000000000) + (16253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120830309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241656833 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16253:ℚ)^(-2:ℤ) : ℝ) = ((16253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1889 : ((((452241664397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16253 < q → q < 16267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16267).mp (by decide +kernel))) hgap
  have hprev := s2L_1888
  have hrat : ((452241664397 : ℚ) / 1000000000000) ≤ ((226120830309 : ℚ) / 500000000000) + (16267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241664397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120830309 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16267:ℚ)^(-2:ℤ) : ℝ) = ((16267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1890 : ((((452241668173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16267 < q → q < 16273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16273).mp (by decide +kernel))) hgap
  have hprev := s2L_1889
  have hrat : ((452241668173 : ℚ) / 1000000000000) ≤ ((452241664397 : ℚ) / 1000000000000) + (16273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241668173 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241664397 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16273:ℚ)^(-2:ℤ) : ℝ) = ((16273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1891 : ((((1766569031 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16273 < q → q < 16301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16301).mp (by decide +kernel))) hgap
  have hprev := s2L_1890
  have hrat : ((1766569031 : ℚ) / 3906250000) ≤ ((452241668173 : ℚ) / 1000000000000) + (16301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1766569031 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((452241668173 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16301:ℚ)^(-2:ℤ) : ℝ) = ((16301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1892 : ((((452241675691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16301 < q → q < 16319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16319).mp (by decide +kernel))) hgap
  have hprev := s2L_1891
  have hrat : ((452241675691 : ℚ) / 1000000000000) ≤ ((1766569031 : ℚ) / 3906250000) + (16319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241675691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1766569031 : ℚ) / 3906250000) : ℚ) : ℝ) + ((16319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16319:ℚ)^(-2:ℤ) : ℝ) = ((16319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1893 : ((((452241679439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16319 < q → q < 16333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16333).mp (by decide +kernel))) hgap
  have hprev := s2L_1892
  have hrat : ((452241679439 : ℚ) / 1000000000000) ≤ ((452241675691 : ℚ) / 1000000000000) + (16333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241679439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241675691 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16333:ℚ)^(-2:ℤ) : ℝ) = ((16333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1894 : ((((28265105199 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16333 < q → q < 16339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16339).mp (by decide +kernel))) hgap
  have hprev := s2L_1893
  have hrat : ((28265105199 : ℚ) / 62500000000) ≤ ((452241679439 : ℚ) / 1000000000000) + (16339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265105199 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452241679439 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16339:ℚ)^(-2:ℤ) : ℝ) = ((16339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1895 : ((((18089667477 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16339 < q → q < 16349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16349).mp (by decide +kernel))) hgap
  have hprev := s2L_1894
  have hrat : ((18089667477 : ℚ) / 40000000000) ≤ ((28265105199 : ℚ) / 62500000000) + (16349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089667477 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((28265105199 : ℚ) / 62500000000) : ℚ) : ℝ) + ((16349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16349:ℚ)^(-2:ℤ) : ℝ) = ((16349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1896 : ((((22612084533 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16349 < q → q < 16361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16361).mp (by decide +kernel))) hgap
  have hprev := s2L_1895
  have hrat : ((22612084533 : ℚ) / 50000000000) ≤ ((18089667477 : ℚ) / 40000000000) + (16361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612084533 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18089667477 : ℚ) / 40000000000) : ℚ) : ℝ) + ((16361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16361:ℚ)^(-2:ℤ) : ℝ) = ((16361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1897 : ((((226120847197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16363, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16361 < q → q < 16363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16363).mp (by decide +kernel))) hgap
  have hprev := s2L_1896
  have hrat : ((226120847197 : ℚ) / 500000000000) ≤ ((22612084533 : ℚ) / 50000000000) + (16363:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120847197 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612084533 : ℚ) / 50000000000) : ℚ) : ℝ) + ((16363:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16363:ℚ)^(-2:ℤ) : ℝ) = ((16363:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1898 : ((((226120849063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16363 < q → q < 16369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16369).mp (by decide +kernel))) hgap
  have hprev := s2L_1897
  have hrat : ((226120849063 : ℚ) / 500000000000) ≤ ((226120847197 : ℚ) / 500000000000) + (16369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120849063 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120847197 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16369:ℚ)^(-2:ℤ) : ℝ) = ((16369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1899 : ((((113060425463 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16369 < q → q < 16381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16381).mp (by decide +kernel))) hgap
  have hprev := s2L_1898
  have hrat : ((113060425463 : ℚ) / 250000000000) ≤ ((226120849063 : ℚ) / 500000000000) + (16381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060425463 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120849063 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16381:ℚ)^(-2:ℤ) : ℝ) = ((16381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1900 : ((((90448341113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16381 < q → q < 16411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16411).mp (by decide +kernel))) hgap
  have hprev := s2L_1899
  have hrat : ((90448341113 : ℚ) / 200000000000) ≤ ((113060425463 : ℚ) / 250000000000) + (16411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448341113 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060425463 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16411:ℚ)^(-2:ℤ) : ℝ) = ((16411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1901 : ((((18089668371 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16411 < q → q < 16417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16417).mp (by decide +kernel))) hgap
  have hprev := s2L_1900
  have hrat : ((18089668371 : ℚ) / 40000000000) ≤ ((90448341113 : ℚ) / 200000000000) + (16417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089668371 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((90448341113 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16417:ℚ)^(-2:ℤ) : ℝ) = ((16417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1902 : ((((452241712983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16417 < q → q < 16421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16421).mp (by decide +kernel))) hgap
  have hprev := s2L_1901
  have hrat : ((452241712983 : ℚ) / 1000000000000) ≤ ((18089668371 : ℚ) / 40000000000) + (16421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241712983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089668371 : ℚ) / 40000000000) : ℚ) : ℝ) + ((16421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16421:ℚ)^(-2:ℤ) : ℝ) = ((16421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1903 : ((((28265107293 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16421 < q → q < 16427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16427).mp (by decide +kernel))) hgap
  have hprev := s2L_1902
  have hrat : ((28265107293 : ℚ) / 62500000000) ≤ ((452241712983 : ℚ) / 1000000000000) + (16427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265107293 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452241712983 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16427:ℚ)^(-2:ℤ) : ℝ) = ((16427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1904 : ((((452241720391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16427 < q → q < 16433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16433).mp (by decide +kernel))) hgap
  have hprev := s2L_1903
  have hrat : ((452241720391 : ℚ) / 1000000000000) ≤ ((28265107293 : ℚ) / 62500000000) + (16433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241720391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265107293 : ℚ) / 62500000000) : ℚ) : ℝ) + ((16433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16433:ℚ)^(-2:ℤ) : ℝ) = ((16433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1905 : ((((452241724087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16433 < q → q < 16447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16447).mp (by decide +kernel))) hgap
  have hprev := s2L_1904
  have hrat : ((452241724087 : ℚ) / 1000000000000) ≤ ((452241720391 : ℚ) / 1000000000000) + (16447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241724087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241720391 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16447:ℚ)^(-2:ℤ) : ℝ) = ((16447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1906 : ((((226120863891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16447 < q → q < 16451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16451).mp (by decide +kernel))) hgap
  have hprev := s2L_1905
  have hrat : ((226120863891 : ℚ) / 500000000000) ≤ ((452241724087 : ℚ) / 1000000000000) + (16451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120863891 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241724087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16451:ℚ)^(-2:ℤ) : ℝ) = ((16451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1907 : ((((113060432869 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16451 < q → q < 16453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16453).mp (by decide +kernel))) hgap
  have hprev := s2L_1906
  have hrat : ((113060432869 : ℚ) / 250000000000) ≤ ((226120863891 : ℚ) / 500000000000) + (16453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060432869 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120863891 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16453:ℚ)^(-2:ℤ) : ℝ) = ((16453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1908 : ((((452241735159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16453 < q → q < 16477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16477).mp (by decide +kernel))) hgap
  have hprev := s2L_1907
  have hrat : ((452241735159 : ℚ) / 1000000000000) ≤ ((113060432869 : ℚ) / 250000000000) + (16477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241735159 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060432869 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16477:ℚ)^(-2:ℤ) : ℝ) = ((16477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1909 : ((((11306043471 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16477 < q → q < 16481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16481).mp (by decide +kernel))) hgap
  have hprev := s2L_1908
  have hrat : ((11306043471 : ℚ) / 25000000000) ≤ ((452241735159 : ℚ) / 1000000000000) + (16481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306043471 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452241735159 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16481:ℚ)^(-2:ℤ) : ℝ) = ((16481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1910 : ((((226120871259 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16481 < q → q < 16487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16487).mp (by decide +kernel))) hgap
  have hprev := s2L_1909
  have hrat : ((226120871259 : ℚ) / 500000000000) ≤ ((11306043471 : ℚ) / 25000000000) + (16487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120871259 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11306043471 : ℚ) / 25000000000) : ℚ) : ℝ) + ((16487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16487:ℚ)^(-2:ℤ) : ℝ) = ((16487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1911 : ((((226120873097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16487 < q → q < 16493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16493).mp (by decide +kernel))) hgap
  have hprev := s2L_1910
  have hrat : ((226120873097 : ℚ) / 500000000000) ≤ ((226120871259 : ℚ) / 500000000000) + (16493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120873097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120871259 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16493:ℚ)^(-2:ℤ) : ℝ) = ((16493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1912 : ((((226120874929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16493 < q → q < 16519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16519).mp (by decide +kernel))) hgap
  have hprev := s2L_1911
  have hrat : ((226120874929 : ℚ) / 500000000000) ≤ ((226120873097 : ℚ) / 500000000000) + (16519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120874929 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120873097 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16519:ℚ)^(-2:ℤ) : ℝ) = ((16519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1913 : ((((226120876759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16519 < q → q < 16529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16529).mp (by decide +kernel))) hgap
  have hprev := s2L_1912
  have hrat : ((226120876759 : ℚ) / 500000000000) ≤ ((226120874929 : ℚ) / 500000000000) + (16529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120876759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120874929 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16529:ℚ)^(-2:ℤ) : ℝ) = ((16529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1914 : ((((45224175717 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16529 < q → q < 16547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16547).mp (by decide +kernel))) hgap
  have hprev := s2L_1913
  have hrat : ((45224175717 : ℚ) / 100000000000) ≤ ((226120876759 : ℚ) / 500000000000) + (16547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224175717 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226120876759 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16547:ℚ)^(-2:ℤ) : ℝ) = ((16547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1915 : ((((452241760819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16547 < q → q < 16553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16553).mp (by decide +kernel))) hgap
  have hprev := s2L_1914
  have hrat : ((452241760819 : ℚ) / 1000000000000) ≤ ((45224175717 : ℚ) / 100000000000) + (16553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241760819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224175717 : ℚ) / 100000000000) : ℚ) : ℝ) + ((16553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16553:ℚ)^(-2:ℤ) : ℝ) = ((16553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1916 : ((((90448352893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16553 < q → q < 16561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16561).mp (by decide +kernel))) hgap
  have hprev := s2L_1915
  have hrat : ((90448352893 : ℚ) / 200000000000) ≤ ((452241760819 : ℚ) / 1000000000000) + (16561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448352893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241760819 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16561:ℚ)^(-2:ℤ) : ℝ) = ((16561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1917 : ((((113060442027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16561 < q → q < 16567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16567).mp (by decide +kernel))) hgap
  have hprev := s2L_1916
  have hrat : ((113060442027 : ℚ) / 250000000000) ≤ ((90448352893 : ℚ) / 200000000000) + (16567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060442027 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448352893 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16567:ℚ)^(-2:ℤ) : ℝ) = ((16567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1918 : ((((113060442937 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16567 < q → q < 16573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16573).mp (by decide +kernel))) hgap
  have hprev := s2L_1917
  have hrat : ((113060442937 : ℚ) / 250000000000) ≤ ((113060442027 : ℚ) / 250000000000) + (16573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060442937 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060442027 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16573:ℚ)^(-2:ℤ) : ℝ) = ((16573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1919 : ((((3617934203 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16573 < q → q < 16603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16603).mp (by decide +kernel))) hgap
  have hprev := s2L_1918
  have hrat : ((3617934203 : ℚ) / 8000000000) ≤ ((113060442937 : ℚ) / 250000000000) + (16603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3617934203 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((113060442937 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16603:ℚ)^(-2:ℤ) : ℝ) = ((16603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1920 : ((((452241779 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16603 < q → q < 16607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16607).mp (by decide +kernel))) hgap
  have hprev := s2L_1919
  have hrat : ((452241779 : ℚ) / 1000000000) ≤ ((3617934203 : ℚ) / 8000000000) + (16607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241779 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ ((((3617934203 : ℚ) / 8000000000) : ℚ) : ℝ) + ((16607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16607:ℚ)^(-2:ℤ) : ℝ) = ((16607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1921 : ((((22612089131 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16607 < q → q < 16619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16619).mp (by decide +kernel))) hgap
  have hprev := s2L_1920
  have hrat : ((22612089131 : ℚ) / 50000000000) ≤ ((452241779 : ℚ) / 1000000000) + (16619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612089131 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452241779 : ℚ) / 1000000000) : ℚ) : ℝ) + ((16619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16619:ℚ)^(-2:ℤ) : ℝ) = ((16619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1922 : ((((90448357247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16619 < q → q < 16631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16631).mp (by decide +kernel))) hgap
  have hprev := s2L_1921
  have hrat : ((90448357247 : ℚ) / 200000000000) ≤ ((22612089131 : ℚ) / 50000000000) + (16631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448357247 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612089131 : ℚ) / 50000000000) : ℚ) : ℝ) + ((16631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16631:ℚ)^(-2:ℤ) : ℝ) = ((16631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1923 : ((((452241789849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16631 < q → q < 16633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16633).mp (by decide +kernel))) hgap
  have hprev := s2L_1922
  have hrat : ((452241789849 : ℚ) / 1000000000000) ≤ ((90448357247 : ℚ) / 200000000000) + (16633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241789849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448357247 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16633:ℚ)^(-2:ℤ) : ℝ) = ((16633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1924 : ((((28265112091 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16633 < q → q < 16649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16649).mp (by decide +kernel))) hgap
  have hprev := s2L_1923
  have hrat : ((28265112091 : ℚ) / 62500000000) ≤ ((452241789849 : ℚ) / 1000000000000) + (16649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265112091 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452241789849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16649:ℚ)^(-2:ℤ) : ℝ) = ((16649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1925 : ((((226120898531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16651, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16649 < q → q < 16651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16651).mp (by decide +kernel))) hgap
  have hprev := s2L_1924
  have hrat : ((226120898531 : ℚ) / 500000000000) ≤ ((28265112091 : ℚ) / 62500000000) + (16651:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120898531 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265112091 : ℚ) / 62500000000) : ℚ) : ℝ) + ((16651:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16651:ℚ)^(-2:ℤ) : ℝ) = ((16651:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1926 : ((((226120900333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16651 < q → q < 16657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16657).mp (by decide +kernel))) hgap
  have hprev := s2L_1925
  have hrat : ((226120900333 : ℚ) / 500000000000) ≤ ((226120898531 : ℚ) / 500000000000) + (16657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120900333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120898531 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16657:ℚ)^(-2:ℤ) : ℝ) = ((16657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1927 : ((((113060451067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16657 < q → q < 16661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16661).mp (by decide +kernel))) hgap
  have hprev := s2L_1926
  have hrat : ((113060451067 : ℚ) / 250000000000) ≤ ((226120900333 : ℚ) / 500000000000) + (16661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060451067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120900333 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16661:ℚ)^(-2:ℤ) : ℝ) = ((16661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1928 : ((((90448361573 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16661 < q → q < 16673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16673).mp (by decide +kernel))) hgap
  have hprev := s2L_1927
  have hrat : ((90448361573 : ℚ) / 200000000000) ≤ ((113060451067 : ℚ) / 250000000000) + (16673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448361573 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060451067 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16673:ℚ)^(-2:ℤ) : ℝ) = ((16673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1929 : ((((226120905727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16673 < q → q < 16691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16691).mp (by decide +kernel))) hgap
  have hprev := s2L_1928
  have hrat : ((226120905727 : ℚ) / 500000000000) ≤ ((90448361573 : ℚ) / 200000000000) + (16691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120905727 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448361573 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16691:ℚ)^(-2:ℤ) : ℝ) = ((16691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1930 : ((((226120907521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16691 < q → q < 16693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16693).mp (by decide +kernel))) hgap
  have hprev := s2L_1929
  have hrat : ((226120907521 : ℚ) / 500000000000) ≤ ((226120905727 : ℚ) / 500000000000) + (16693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120907521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120905727 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16693:ℚ)^(-2:ℤ) : ℝ) = ((16693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1931 : ((((113060454657 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16693 < q → q < 16699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16699).mp (by decide +kernel))) hgap
  have hprev := s2L_1930
  have hrat : ((113060454657 : ℚ) / 250000000000) ≤ ((226120907521 : ℚ) / 500000000000) + (16699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060454657 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120907521 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16699:ℚ)^(-2:ℤ) : ℝ) = ((16699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1932 : ((((113060455553 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16699 < q → q < 16703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16703).mp (by decide +kernel))) hgap
  have hprev := s2L_1931
  have hrat : ((113060455553 : ℚ) / 250000000000) ≤ ((113060454657 : ℚ) / 250000000000) + (16703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060455553 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060454657 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16703:ℚ)^(-2:ℤ) : ℝ) = ((16703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1933 : ((((90448365157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16703 < q → q < 16729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16729).mp (by decide +kernel))) hgap
  have hprev := s2L_1932
  have hrat : ((90448365157 : ℚ) / 200000000000) ≤ ((113060455553 : ℚ) / 250000000000) + (16729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448365157 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060455553 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16729:ℚ)^(-2:ℤ) : ℝ) = ((16729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1934 : ((((452241829353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16729 < q → q < 16741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16741).mp (by decide +kernel))) hgap
  have hprev := s2L_1933
  have hrat : ((452241829353 : ℚ) / 1000000000000) ≤ ((90448365157 : ℚ) / 200000000000) + (16741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241829353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448365157 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16741:ℚ)^(-2:ℤ) : ℝ) = ((16741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1935 : ((((226120916459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16741 < q → q < 16747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16747).mp (by decide +kernel))) hgap
  have hprev := s2L_1934
  have hrat : ((226120916459 : ℚ) / 500000000000) ≤ ((452241829353 : ℚ) / 1000000000000) + (16747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120916459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241829353 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16747:ℚ)^(-2:ℤ) : ℝ) = ((16747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1936 : ((((226120918239 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16747 < q → q < 16759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16759).mp (by decide +kernel))) hgap
  have hprev := s2L_1935
  have hrat : ((226120918239 : ℚ) / 500000000000) ≤ ((226120916459 : ℚ) / 500000000000) + (16759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120918239 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120916459 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16759:ℚ)^(-2:ℤ) : ℝ) = ((16759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1937 : ((((113060460009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16759 < q → q < 16763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16763).mp (by decide +kernel))) hgap
  have hprev := s2L_1936
  have hrat : ((113060460009 : ℚ) / 250000000000) ≤ ((226120918239 : ℚ) / 500000000000) + (16763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060460009 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226120918239 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16763:ℚ)^(-2:ℤ) : ℝ) = ((16763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1938 : ((((3533139403 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16763 < q → q < 16787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16787).mp (by decide +kernel))) hgap
  have hprev := s2L_1937
  have hrat : ((3533139403 : ℚ) / 7812500000) ≤ ((113060460009 : ℚ) / 250000000000) + (16787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533139403 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((113060460009 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16787:ℚ)^(-2:ℤ) : ℝ) = ((16787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1939 : ((((226120923561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16811, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16787 < q → q < 16811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16811).mp (by decide +kernel))) hgap
  have hprev := s2L_1938
  have hrat : ((226120923561 : ℚ) / 500000000000) ≤ ((3533139403 : ℚ) / 7812500000) + (16811:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120923561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((3533139403 : ℚ) / 7812500000) : ℚ) : ℝ) + ((16811:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16811:ℚ)^(-2:ℤ) : ℝ) = ((16811:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1940 : ((((90448370131 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16811 < q → q < 16823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16823).mp (by decide +kernel))) hgap
  have hprev := s2L_1939
  have hrat : ((90448370131 : ℚ) / 200000000000) ≤ ((226120923561 : ℚ) / 500000000000) + (16823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448370131 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226120923561 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16823:ℚ)^(-2:ℤ) : ℝ) = ((16823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1941 : ((((90448370837 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16823 < q → q < 16829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16829).mp (by decide +kernel))) hgap
  have hprev := s2L_1940
  have hrat : ((90448370837 : ℚ) / 200000000000) ≤ ((90448370131 : ℚ) / 200000000000) + (16829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448370837 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448370131 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16829:ℚ)^(-2:ℤ) : ℝ) = ((16829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1942 : ((((90448371543 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16829 < q → q < 16831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16831).mp (by decide +kernel))) hgap
  have hprev := s2L_1941
  have hrat : ((90448371543 : ℚ) / 200000000000) ≤ ((90448370837 : ℚ) / 200000000000) + (16831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448371543 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448370837 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16831:ℚ)^(-2:ℤ) : ℝ) = ((16831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1943 : ((((11306046531 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16831 < q → q < 16843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16843).mp (by decide +kernel))) hgap
  have hprev := s2L_1942
  have hrat : ((11306046531 : ℚ) / 25000000000) ≤ ((90448371543 : ℚ) / 200000000000) + (16843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306046531 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((90448371543 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16843:ℚ)^(-2:ℤ) : ℝ) = ((16843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1944 : ((((452241864753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16843 < q → q < 16871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16871).mp (by decide +kernel))) hgap
  have hprev := s2L_1943
  have hrat : ((452241864753 : ℚ) / 1000000000000) ≤ ((11306046531 : ℚ) / 25000000000) + (16871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241864753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306046531 : ℚ) / 25000000000) : ℚ) : ℝ) + ((16871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16871:ℚ)^(-2:ℤ) : ℝ) = ((16871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1945 : ((((226120934131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16871 < q → q < 16879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16879).mp (by decide +kernel))) hgap
  have hprev := s2L_1944
  have hrat : ((226120934131 : ℚ) / 500000000000) ≤ ((452241864753 : ℚ) / 1000000000000) + (16879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120934131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241864753 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16879:ℚ)^(-2:ℤ) : ℝ) = ((16879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1946 : ((((45224187177 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16879 < q → q < 16883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16883).mp (by decide +kernel))) hgap
  have hprev := s2L_1945
  have hrat : ((45224187177 : ℚ) / 100000000000) ≤ ((226120934131 : ℚ) / 500000000000) + (16883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224187177 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226120934131 : ℚ) / 500000000000) : ℚ) : ℝ) + ((16883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16883:ℚ)^(-2:ℤ) : ℝ) = ((16883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1947 : ((((18089675011 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16883 < q → q < 16889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16889).mp (by decide +kernel))) hgap
  have hprev := s2L_1946
  have hrat : ((18089675011 : ℚ) / 40000000000) ≤ ((45224187177 : ℚ) / 100000000000) + (16889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089675011 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((45224187177 : ℚ) / 100000000000) : ℚ) : ℝ) + ((16889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16889:ℚ)^(-2:ℤ) : ℝ) = ((16889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1948 : ((((18089675151 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16889 < q → q < 16901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16901).mp (by decide +kernel))) hgap
  have hprev := s2L_1947
  have hrat : ((18089675151 : ℚ) / 40000000000) ≤ ((18089675011 : ℚ) / 40000000000) + (16901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089675151 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((18089675011 : ℚ) / 40000000000) : ℚ) : ℝ) + ((16901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16901:ℚ)^(-2:ℤ) : ℝ) = ((16901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1949 : ((((18089675291 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16901 < q → q < 16903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16903).mp (by decide +kernel))) hgap
  have hprev := s2L_1948
  have hrat : ((18089675291 : ℚ) / 40000000000) ≤ ((18089675151 : ℚ) / 40000000000) + (16903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089675291 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((18089675151 : ℚ) / 40000000000) : ℚ) : ℝ) + ((16903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16903:ℚ)^(-2:ℤ) : ℝ) = ((16903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1950 : ((((452241885767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16903 < q → q < 16921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16921).mp (by decide +kernel))) hgap
  have hprev := s2L_1949
  have hrat : ((452241885767 : ℚ) / 1000000000000) ≤ ((18089675291 : ℚ) / 40000000000) + (16921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241885767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089675291 : ℚ) / 40000000000) : ℚ) : ℝ) + ((16921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16921:ℚ)^(-2:ℤ) : ℝ) = ((16921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1951 : ((((452241889257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16921 < q → q < 16927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16927).mp (by decide +kernel))) hgap
  have hprev := s2L_1950
  have hrat : ((452241889257 : ℚ) / 1000000000000) ≤ ((452241885767 : ℚ) / 1000000000000) + (16927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241889257 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241885767 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16927:ℚ)^(-2:ℤ) : ℝ) = ((16927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1952 : ((((90448378549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16927 < q → q < 16931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16931).mp (by decide +kernel))) hgap
  have hprev := s2L_1951
  have hrat : ((90448378549 : ℚ) / 200000000000) ≤ ((452241889257 : ℚ) / 1000000000000) + (16931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448378549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452241889257 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16931:ℚ)^(-2:ℤ) : ℝ) = ((16931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1953 : ((((45224189623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16931 < q → q < 16937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16937).mp (by decide +kernel))) hgap
  have hprev := s2L_1952
  have hrat : ((45224189623 : ℚ) / 100000000000) ≤ ((90448378549 : ℚ) / 200000000000) + (16937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224189623 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90448378549 : ℚ) / 200000000000) : ℚ) : ℝ) + ((16937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16937:ℚ)^(-2:ℤ) : ℝ) = ((16937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1954 : ((((452241899713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16937 < q → q < 16943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16943).mp (by decide +kernel))) hgap
  have hprev := s2L_1953
  have hrat : ((452241899713 : ℚ) / 1000000000000) ≤ ((45224189623 : ℚ) / 100000000000) + (16943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241899713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224189623 : ℚ) / 100000000000) : ℚ) : ℝ) + ((16943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16943:ℚ)^(-2:ℤ) : ℝ) = ((16943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1955 : ((((113060475797 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16943 < q → q < 16963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16963).mp (by decide +kernel))) hgap
  have hprev := s2L_1954
  have hrat : ((113060475797 : ℚ) / 250000000000) ≤ ((452241899713 : ℚ) / 1000000000000) + (16963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060475797 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241899713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16963:ℚ)^(-2:ℤ) : ℝ) = ((16963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1956 : ((((14132559583 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16963 < q → q < 16979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16979).mp (by decide +kernel))) hgap
  have hprev := s2L_1955
  have hrat : ((14132559583 : ℚ) / 31250000000) ≤ ((113060475797 : ℚ) / 250000000000) + (16979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132559583 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113060475797 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16979:ℚ)^(-2:ℤ) : ℝ) = ((16979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1957 : ((((452241910123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16979 < q → q < 16981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16981).mp (by decide +kernel))) hgap
  have hprev := s2L_1956
  have hrat : ((452241910123 : ℚ) / 1000000000000) ≤ ((14132559583 : ℚ) / 31250000000) + (16981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241910123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132559583 : ℚ) / 31250000000) : ℚ) : ℝ) + ((16981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16981:ℚ)^(-2:ℤ) : ℝ) = ((16981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1958 : ((((113060478397 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16981 < q → q < 16987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16987).mp (by decide +kernel))) hgap
  have hprev := s2L_1957
  have hrat : ((113060478397 : ℚ) / 250000000000) ≤ ((452241910123 : ℚ) / 1000000000000) + (16987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060478397 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241910123 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((16987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16987:ℚ)^(-2:ℤ) : ℝ) = ((16987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1959 : ((((452241917051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 16993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16987 < q → q < 16993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 16993).mp (by decide +kernel))) hgap
  have hprev := s2L_1958
  have hrat : ((452241917051 : ℚ) / 1000000000000) ≤ ((113060478397 : ℚ) / 250000000000) + (16993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241917051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060478397 : ℚ) / 250000000000) : ℚ) : ℝ) + ((16993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((16993:ℚ)^(-2:ℤ) : ℝ) = ((16993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1960 : ((((226120960253 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 16993 < q → q < 17011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17011).mp (by decide +kernel))) hgap
  have hprev := s2L_1959
  have hrat : ((226120960253 : ℚ) / 500000000000) ≤ ((452241917051 : ℚ) / 1000000000000) + (17011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120960253 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241917051 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17011:ℚ)^(-2:ℤ) : ℝ) = ((17011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1961 : ((((452241923957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17011 < q → q < 17021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17021).mp (by decide +kernel))) hgap
  have hprev := s2L_1960
  have hrat : ((452241923957 : ℚ) / 1000000000000) ≤ ((226120960253 : ℚ) / 500000000000) + (17021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241923957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120960253 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17021:ℚ)^(-2:ℤ) : ℝ) = ((17021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1962 : ((((226120963703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17021 < q → q < 17027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17027).mp (by decide +kernel))) hgap
  have hprev := s2L_1961
  have hrat : ((226120963703 : ℚ) / 500000000000) ≤ ((452241923957 : ℚ) / 1000000000000) + (17027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120963703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241923957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17027:ℚ)^(-2:ℤ) : ℝ) = ((17027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1963 : ((((226120965427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17027 < q → q < 17029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17029).mp (by decide +kernel))) hgap
  have hprev := s2L_1962
  have hrat : ((226120965427 : ℚ) / 500000000000) ≤ ((226120963703 : ℚ) / 500000000000) + (17029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120965427 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120963703 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17029:ℚ)^(-2:ℤ) : ℝ) = ((17029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1964 : ((((4522419343 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17029 < q → q < 17033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17033).mp (by decide +kernel))) hgap
  have hprev := s2L_1963
  have hrat : ((4522419343 : ℚ) / 10000000000) ≤ ((226120965427 : ℚ) / 500000000000) + (17033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522419343 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226120965427 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17033:ℚ)^(-2:ℤ) : ℝ) = ((17033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1965 : ((((452241937743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17033 < q → q < 17041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17041).mp (by decide +kernel))) hgap
  have hprev := s2L_1964
  have hrat : ((452241937743 : ℚ) / 1000000000000) ≤ ((4522419343 : ℚ) / 10000000000) + (17041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241937743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522419343 : ℚ) / 10000000000) : ℚ) : ℝ) + ((17041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17041:ℚ)^(-2:ℤ) : ℝ) = ((17041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1966 : ((((7066280331 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17041 < q → q < 17047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17047).mp (by decide +kernel))) hgap
  have hprev := s2L_1965
  have hrat : ((7066280331 : ℚ) / 15625000000) ≤ ((452241937743 : ℚ) / 1000000000000) + (17047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066280331 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452241937743 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17047:ℚ)^(-2:ℤ) : ℝ) = ((17047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1967 : ((((226120972311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17047 < q → q < 17053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17053).mp (by decide +kernel))) hgap
  have hprev := s2L_1966
  have hrat : ((226120972311 : ℚ) / 500000000000) ≤ ((7066280331 : ℚ) / 15625000000) + (17053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120972311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7066280331 : ℚ) / 15625000000) : ℚ) : ℝ) + ((17053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17053:ℚ)^(-2:ℤ) : ℝ) = ((17053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1968 : ((((452241948051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17053 < q → q < 17077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17077).mp (by decide +kernel))) hgap
  have hprev := s2L_1967
  have hrat : ((452241948051 : ℚ) / 1000000000000) ≤ ((226120972311 : ℚ) / 500000000000) + (17077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241948051 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120972311 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17077:ℚ)^(-2:ℤ) : ℝ) = ((17077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1969 : ((((452241951473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17077 < q → q < 17093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17093).mp (by decide +kernel))) hgap
  have hprev := s2L_1968
  have hrat : ((452241951473 : ℚ) / 1000000000000) ≤ ((452241948051 : ℚ) / 1000000000000) + (17093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241951473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241948051 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17093:ℚ)^(-2:ℤ) : ℝ) = ((17093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1970 : ((((452241954893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17093 < q → q < 17099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17099).mp (by decide +kernel))) hgap
  have hprev := s2L_1969
  have hrat : ((452241954893 : ℚ) / 1000000000000) ≤ ((452241951473 : ℚ) / 1000000000000) + (17099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241954893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241951473 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17099:ℚ)^(-2:ℤ) : ℝ) = ((17099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1971 : ((((45224195831 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17099 < q → q < 17107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17107).mp (by decide +kernel))) hgap
  have hprev := s2L_1970
  have hrat : ((45224195831 : ℚ) / 100000000000) ≤ ((452241954893 : ℚ) / 1000000000000) + (17107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224195831 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452241954893 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17107:ℚ)^(-2:ℤ) : ℝ) = ((17107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1972 : ((((452241961723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17107 < q → q < 17117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17117).mp (by decide +kernel))) hgap
  have hprev := s2L_1971
  have hrat : ((452241961723 : ℚ) / 1000000000000) ≤ ((45224195831 : ℚ) / 100000000000) + (17117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241961723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224195831 : ℚ) / 100000000000) : ℚ) : ℝ) + ((17117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17117:ℚ)^(-2:ℤ) : ℝ) = ((17117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1973 : ((((452241965133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17117 < q → q < 17123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17123).mp (by decide +kernel))) hgap
  have hprev := s2L_1972
  have hrat : ((452241965133 : ℚ) / 1000000000000) ≤ ((452241961723 : ℚ) / 1000000000000) + (17123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241965133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241961723 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17123:ℚ)^(-2:ℤ) : ℝ) = ((17123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1974 : ((((226120984269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17123 < q → q < 17137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17137).mp (by decide +kernel))) hgap
  have hprev := s2L_1973
  have hrat : ((226120984269 : ℚ) / 500000000000) ≤ ((452241965133 : ℚ) / 1000000000000) + (17137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120984269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452241965133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17137:ℚ)^(-2:ℤ) : ℝ) = ((17137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1975 : ((((226120985967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17137 < q → q < 17159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17159).mp (by decide +kernel))) hgap
  have hprev := s2L_1974
  have hrat : ((226120985967 : ℚ) / 500000000000) ≤ ((226120984269 : ℚ) / 500000000000) + (17159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120985967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120984269 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17159:ℚ)^(-2:ℤ) : ℝ) = ((17159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1976 : ((((452241975327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17159 < q → q < 17167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17167).mp (by decide +kernel))) hgap
  have hprev := s2L_1975
  have hrat : ((452241975327 : ℚ) / 1000000000000) ≤ ((226120985967 : ℚ) / 500000000000) + (17167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241975327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120985967 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17167:ℚ)^(-2:ℤ) : ℝ) = ((17167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1977 : ((((452241978713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17167 < q → q < 17183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17183).mp (by decide +kernel))) hgap
  have hprev := s2L_1976
  have hrat : ((452241978713 : ℚ) / 1000000000000) ≤ ((452241975327 : ℚ) / 1000000000000) + (17183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241978713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241975327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17183:ℚ)^(-2:ℤ) : ℝ) = ((17183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1978 : ((((452241982097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17183 < q → q < 17189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17189).mp (by decide +kernel))) hgap
  have hprev := s2L_1977
  have hrat : ((452241982097 : ℚ) / 1000000000000) ≤ ((452241978713 : ℚ) / 1000000000000) + (17189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241982097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452241978713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17189:ℚ)^(-2:ℤ) : ℝ) = ((17189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1979 : ((((11306049637 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17189 < q → q < 17191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17191).mp (by decide +kernel))) hgap
  have hprev := s2L_1978
  have hrat : ((11306049637 : ℚ) / 25000000000) ≤ ((452241982097 : ℚ) / 1000000000000) + (17191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306049637 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452241982097 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17191:ℚ)^(-2:ℤ) : ℝ) = ((17191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1980 : ((((452241988859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17191 < q → q < 17203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17203).mp (by decide +kernel))) hgap
  have hprev := s2L_1979
  have hrat : ((452241988859 : ℚ) / 1000000000000) ≤ ((11306049637 : ℚ) / 25000000000) + (17203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452241988859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306049637 : ℚ) / 25000000000) : ℚ) : ℝ) + ((17203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17203:ℚ)^(-2:ℤ) : ℝ) = ((17203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1981 : ((((113060498059 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17203 < q → q < 17207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17207).mp (by decide +kernel))) hgap
  have hprev := s2L_1980
  have hrat : ((113060498059 : ℚ) / 250000000000) ≤ ((452241988859 : ℚ) / 1000000000000) + (17207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060498059 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452241988859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17207:ℚ)^(-2:ℤ) : ℝ) = ((17207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1982 : ((((113060498903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17207 < q → q < 17209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17209).mp (by decide +kernel))) hgap
  have hprev := s2L_1981
  have hrat : ((113060498903 : ℚ) / 250000000000) ≤ ((113060498059 : ℚ) / 250000000000) + (17209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060498903 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060498059 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17209:ℚ)^(-2:ℤ) : ℝ) = ((17209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1983 : ((((22612099949 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17209 < q → q < 17231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17231).mp (by decide +kernel))) hgap
  have hprev := s2L_1982
  have hrat : ((22612099949 : ℚ) / 50000000000) ≤ ((113060498903 : ℚ) / 250000000000) + (17231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612099949 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113060498903 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17231:ℚ)^(-2:ℤ) : ℝ) = ((17231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1984 : ((((56530250293 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17231 < q → q < 17239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17239).mp (by decide +kernel))) hgap
  have hprev := s2L_1983
  have hrat : ((56530250293 : ℚ) / 125000000000) ≤ ((22612099949 : ℚ) / 50000000000) + (17239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530250293 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22612099949 : ℚ) / 50000000000) : ℚ) : ℝ) + ((17239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17239:ℚ)^(-2:ℤ) : ℝ) = ((17239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1985 : ((((452242005701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17239 < q → q < 17257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17257).mp (by decide +kernel))) hgap
  have hprev := s2L_1984
  have hrat : ((452242005701 : ℚ) / 1000000000000) ≤ ((56530250293 : ℚ) / 125000000000) + (17257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242005701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530250293 : ℚ) / 125000000000) : ℚ) : ℝ) + ((17257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17257:ℚ)^(-2:ℤ) : ℝ) = ((17257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1986 : ((((90448401809 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17257 < q → q < 17291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17291).mp (by decide +kernel))) hgap
  have hprev := s2L_1985
  have hrat : ((90448401809 : ℚ) / 200000000000) ≤ ((452242005701 : ℚ) / 1000000000000) + (17291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448401809 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242005701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17291:ℚ)^(-2:ℤ) : ℝ) = ((17291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1987 : ((((113060503097 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17291 < q → q < 17293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17293).mp (by decide +kernel))) hgap
  have hprev := s2L_1986
  have hrat : ((113060503097 : ℚ) / 250000000000) ≤ ((90448401809 : ℚ) / 200000000000) + (17293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060503097 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448401809 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17293:ℚ)^(-2:ℤ) : ℝ) = ((17293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1988 : ((((452242015729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17293 < q → q < 17299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17299).mp (by decide +kernel))) hgap
  have hprev := s2L_1987
  have hrat : ((452242015729 : ℚ) / 1000000000000) ≤ ((113060503097 : ℚ) / 250000000000) + (17299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242015729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060503097 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17299:ℚ)^(-2:ℤ) : ℝ) = ((17299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1989 : ((((452242019063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17299 < q → q < 17317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17317).mp (by decide +kernel))) hgap
  have hprev := s2L_1988
  have hrat : ((452242019063 : ℚ) / 1000000000000) ≤ ((452242015729 : ℚ) / 1000000000000) + (17317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242019063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242015729 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17317:ℚ)^(-2:ℤ) : ℝ) = ((17317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1990 : ((((113060505599 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17317 < q → q < 17321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17321).mp (by decide +kernel))) hgap
  have hprev := s2L_1989
  have hrat : ((113060505599 : ℚ) / 250000000000) ≤ ((452242019063 : ℚ) / 1000000000000) + (17321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060505599 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242019063 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17321:ℚ)^(-2:ℤ) : ℝ) = ((17321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1991 : ((((226121012863 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17321 < q → q < 17327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17327).mp (by decide +kernel))) hgap
  have hprev := s2L_1990
  have hrat : ((226121012863 : ℚ) / 500000000000) ≤ ((113060505599 : ℚ) / 250000000000) + (17327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121012863 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060505599 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17327:ℚ)^(-2:ℤ) : ℝ) = ((17327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1992 : ((((226121014527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17327 < q → q < 17333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17333).mp (by decide +kernel))) hgap
  have hprev := s2L_1991
  have hrat : ((226121014527 : ℚ) / 500000000000) ≤ ((226121012863 : ℚ) / 500000000000) + (17333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121014527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121012863 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17333:ℚ)^(-2:ℤ) : ℝ) = ((17333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1993 : ((((452242032379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17333 < q → q < 17341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17341).mp (by decide +kernel))) hgap
  have hprev := s2L_1992
  have hrat : ((452242032379 : ℚ) / 1000000000000) ≤ ((226121014527 : ℚ) / 500000000000) + (17341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242032379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121014527 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17341:ℚ)^(-2:ℤ) : ℝ) = ((17341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1994 : ((((4522420357 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17341 < q → q < 17351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17351).mp (by decide +kernel))) hgap
  have hprev := s2L_1993
  have hrat : ((4522420357 : ℚ) / 10000000000) ≤ ((452242032379 : ℚ) / 1000000000000) + (17351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522420357 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452242032379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17351:ℚ)^(-2:ℤ) : ℝ) = ((17351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1995 : ((((226121019509 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17351 < q → q < 17359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17359).mp (by decide +kernel))) hgap
  have hprev := s2L_1994
  have hrat : ((226121019509 : ℚ) / 500000000000) ≤ ((4522420357 : ℚ) / 10000000000) + (17359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121019509 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522420357 : ℚ) / 10000000000) : ℚ) : ℝ) + ((17359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17359:ℚ)^(-2:ℤ) : ℝ) = ((17359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1996 : ((((452242042329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17359 < q → q < 17377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17377).mp (by decide +kernel))) hgap
  have hprev := s2L_1995
  have hrat : ((452242042329 : ℚ) / 1000000000000) ≤ ((226121019509 : ℚ) / 500000000000) + (17377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242042329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121019509 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17377:ℚ)^(-2:ℤ) : ℝ) = ((17377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1997 : ((((226121022819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17377 < q → q < 17383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17383).mp (by decide +kernel))) hgap
  have hprev := s2L_1996
  have hrat : ((226121022819 : ℚ) / 500000000000) ≤ ((452242042329 : ℚ) / 1000000000000) + (17383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121022819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242042329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17383:ℚ)^(-2:ℤ) : ℝ) = ((17383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1998 : ((((90448409789 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17383 < q → q < 17387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17387).mp (by decide +kernel))) hgap
  have hprev := s2L_1997
  have hrat : ((90448409789 : ℚ) / 200000000000) ≤ ((226121022819 : ℚ) / 500000000000) + (17387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448409789 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121022819 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17387:ℚ)^(-2:ℤ) : ℝ) = ((17387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1999 : ((((113060513063 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17387 < q → q < 17389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17389).mp (by decide +kernel))) hgap
  have hprev := s2L_1998
  have hrat : ((113060513063 : ℚ) / 250000000000) ≤ ((90448409789 : ℚ) / 200000000000) + (17389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060513063 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448409789 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17389:ℚ)^(-2:ℤ) : ℝ) = ((17389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2000 : ((((452242055557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17389 < q → q < 17393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17393).mp (by decide +kernel))) hgap
  have hprev := s2L_1999
  have hrat : ((452242055557 : ℚ) / 1000000000000) ≤ ((113060513063 : ℚ) / 250000000000) + (17393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242055557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060513063 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17393:ℚ)^(-2:ℤ) : ℝ) = ((17393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2001 : ((((452242058859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17393 < q → q < 17401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17401).mp (by decide +kernel))) hgap
  have hprev := s2L_2000
  have hrat : ((452242058859 : ℚ) / 1000000000000) ≤ ((452242055557 : ℚ) / 1000000000000) + (17401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242058859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242055557 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17401:ℚ)^(-2:ℤ) : ℝ) = ((17401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2002 : ((((90448412431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17401 < q → q < 17417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17417).mp (by decide +kernel))) hgap
  have hprev := s2L_2001
  have hrat : ((90448412431 : ℚ) / 200000000000) ≤ ((452242058859 : ℚ) / 1000000000000) + (17417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448412431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242058859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17417:ℚ)^(-2:ℤ) : ℝ) = ((17417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2003 : ((((9044841309 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17417 < q → q < 17419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17419).mp (by decide +kernel))) hgap
  have hprev := s2L_2002
  have hrat : ((9044841309 : ℚ) / 20000000000) ≤ ((90448412431 : ℚ) / 200000000000) + (17419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044841309 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((90448412431 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17419:ℚ)^(-2:ℤ) : ℝ) = ((17419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2004 : ((((452242068741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17419 < q → q < 17431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17431).mp (by decide +kernel))) hgap
  have hprev := s2L_2003
  have hrat : ((452242068741 : ℚ) / 1000000000000) ≤ ((9044841309 : ℚ) / 20000000000) + (17431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242068741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044841309 : ℚ) / 20000000000) : ℚ) : ℝ) + ((17431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17431:ℚ)^(-2:ℤ) : ℝ) = ((17431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2005 : ((((452242072027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17431 < q → q < 17443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17443).mp (by decide +kernel))) hgap
  have hprev := s2L_2004
  have hrat : ((452242072027 : ℚ) / 1000000000000) ≤ ((452242068741 : ℚ) / 1000000000000) + (17443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242072027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242068741 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17443:ℚ)^(-2:ℤ) : ℝ) = ((17443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2006 : ((((452242075311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17443 < q → q < 17449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17449).mp (by decide +kernel))) hgap
  have hprev := s2L_2005
  have hrat : ((452242075311 : ℚ) / 1000000000000) ≤ ((452242072027 : ℚ) / 1000000000000) + (17449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242075311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242072027 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17449:ℚ)^(-2:ℤ) : ℝ) = ((17449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2007 : ((((113060519647 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17449 < q → q < 17467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17467).mp (by decide +kernel))) hgap
  have hprev := s2L_2006
  have hrat : ((113060519647 : ℚ) / 250000000000) ≤ ((452242075311 : ℚ) / 1000000000000) + (17467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060519647 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242075311 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17467:ℚ)^(-2:ℤ) : ℝ) = ((17467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2008 : ((((56530260233 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17467 < q → q < 17471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17471).mp (by decide +kernel))) hgap
  have hprev := s2L_2007
  have hrat : ((56530260233 : ℚ) / 125000000000) ≤ ((113060519647 : ℚ) / 250000000000) + (17471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530260233 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060519647 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17471:ℚ)^(-2:ℤ) : ℝ) = ((17471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2009 : ((((452242085137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17471 < q → q < 17477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17477).mp (by decide +kernel))) hgap
  have hprev := s2L_2008
  have hrat : ((452242085137 : ℚ) / 1000000000000) ≤ ((56530260233 : ℚ) / 125000000000) + (17477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242085137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530260233 : ℚ) / 125000000000) : ℚ) : ℝ) + ((17477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17477:ℚ)^(-2:ℤ) : ℝ) = ((17477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2010 : ((((56530261051 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17477 < q → q < 17483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17483).mp (by decide +kernel))) hgap
  have hprev := s2L_2009
  have hrat : ((56530261051 : ℚ) / 125000000000) ≤ ((452242085137 : ℚ) / 1000000000000) + (17483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530261051 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242085137 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17483:ℚ)^(-2:ℤ) : ℝ) = ((17483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2011 : ((((452242091677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17483 < q → q < 17489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17489).mp (by decide +kernel))) hgap
  have hprev := s2L_2010
  have hrat : ((452242091677 : ℚ) / 1000000000000) ≤ ((56530261051 : ℚ) / 125000000000) + (17489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242091677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530261051 : ℚ) / 125000000000) : ℚ) : ℝ) + ((17489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17489:ℚ)^(-2:ℤ) : ℝ) = ((17489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2012 : ((((90448418989 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17489 < q → q < 17491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17491).mp (by decide +kernel))) hgap
  have hprev := s2L_2011
  have hrat : ((90448418989 : ℚ) / 200000000000) ≤ ((452242091677 : ℚ) / 1000000000000) + (17491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448418989 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242091677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17491:ℚ)^(-2:ℤ) : ℝ) = ((17491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2013 : ((((452242098211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17491 < q → q < 17497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17497).mp (by decide +kernel))) hgap
  have hprev := s2L_2012
  have hrat : ((452242098211 : ℚ) / 1000000000000) ≤ ((90448418989 : ℚ) / 200000000000) + (17497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242098211 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448418989 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17497:ℚ)^(-2:ℤ) : ℝ) = ((17497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2014 : ((((14132565671 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17497 < q → q < 17509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17509).mp (by decide +kernel))) hgap
  have hprev := s2L_2013
  have hrat : ((14132565671 : ℚ) / 31250000000) ≤ ((452242098211 : ℚ) / 1000000000000) + (17509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132565671 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452242098211 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17509:ℚ)^(-2:ℤ) : ℝ) = ((17509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2015 : ((((45224210473 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17509 < q → q < 17519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17519).mp (by decide +kernel))) hgap
  have hprev := s2L_2014
  have hrat : ((45224210473 : ℚ) / 100000000000) ≤ ((14132565671 : ℚ) / 31250000000) + (17519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224210473 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((14132565671 : ℚ) / 31250000000) : ℚ) : ℝ) + ((17519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17519:ℚ)^(-2:ℤ) : ℝ) = ((17519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2016 : ((((22612105399 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17519 < q → q < 17539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17539).mp (by decide +kernel))) hgap
  have hprev := s2L_2015
  have hrat : ((22612105399 : ℚ) / 50000000000) ≤ ((45224210473 : ℚ) / 100000000000) + (17539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612105399 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((45224210473 : ℚ) / 100000000000) : ℚ) : ℝ) + ((17539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17539:ℚ)^(-2:ℤ) : ℝ) = ((17539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2017 : ((((226121055613 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17539 < q → q < 17551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17551).mp (by decide +kernel))) hgap
  have hprev := s2L_2016
  have hrat : ((226121055613 : ℚ) / 500000000000) ≤ ((22612105399 : ℚ) / 50000000000) + (17551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121055613 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612105399 : ℚ) / 50000000000) : ℚ) : ℝ) + ((17551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17551:ℚ)^(-2:ℤ) : ℝ) = ((17551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2018 : ((((90448422893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17551 < q → q < 17569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17569).mp (by decide +kernel))) hgap
  have hprev := s2L_2017
  have hrat : ((90448422893 : ℚ) / 200000000000) ≤ ((226121055613 : ℚ) / 500000000000) + (17569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448422893 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121055613 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17569:ℚ)^(-2:ℤ) : ℝ) = ((17569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2019 : ((((452242117703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17569 < q → q < 17573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17573).mp (by decide +kernel))) hgap
  have hprev := s2L_2018
  have hrat : ((452242117703 : ℚ) / 1000000000000) ≤ ((90448422893 : ℚ) / 200000000000) + (17573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242117703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448422893 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17573:ℚ)^(-2:ℤ) : ℝ) = ((17573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2020 : ((((452242120939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17573 < q → q < 17579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17579).mp (by decide +kernel))) hgap
  have hprev := s2L_2019
  have hrat : ((452242120939 : ℚ) / 1000000000000) ≤ ((452242117703 : ℚ) / 1000000000000) + (17579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242120939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242117703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17579:ℚ)^(-2:ℤ) : ℝ) = ((17579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2021 : ((((226121062087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17579 < q → q < 17581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17581).mp (by decide +kernel))) hgap
  have hprev := s2L_2020
  have hrat : ((226121062087 : ℚ) / 500000000000) ≤ ((452242120939 : ℚ) / 1000000000000) + (17581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121062087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242120939 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17581:ℚ)^(-2:ℤ) : ℝ) = ((17581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2022 : ((((452242127403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17581 < q → q < 17597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17597).mp (by decide +kernel))) hgap
  have hprev := s2L_2021
  have hrat : ((452242127403 : ℚ) / 1000000000000) ≤ ((226121062087 : ℚ) / 500000000000) + (17597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242127403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121062087 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17597:ℚ)^(-2:ℤ) : ℝ) = ((17597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2023 : ((((452242130631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17597 < q → q < 17599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17599).mp (by decide +kernel))) hgap
  have hprev := s2L_2022
  have hrat : ((452242130631 : ℚ) / 1000000000000) ≤ ((452242127403 : ℚ) / 1000000000000) + (17599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242130631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242127403 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17599:ℚ)^(-2:ℤ) : ℝ) = ((17599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2024 : ((((14132566683 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17599 < q → q < 17609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17609).mp (by decide +kernel))) hgap
  have hprev := s2L_2023
  have hrat : ((14132566683 : ℚ) / 31250000000) ≤ ((452242130631 : ℚ) / 1000000000000) + (17609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132566683 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452242130631 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17609:ℚ)^(-2:ℤ) : ℝ) = ((17609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2025 : ((((18089685483 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17609 < q → q < 17623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17623).mp (by decide +kernel))) hgap
  have hprev := s2L_2024
  have hrat : ((18089685483 : ℚ) / 40000000000) ≤ ((14132566683 : ℚ) / 31250000000) + (17623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089685483 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((14132566683 : ℚ) / 31250000000) : ℚ) : ℝ) + ((17623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17623:ℚ)^(-2:ℤ) : ℝ) = ((17623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2026 : ((((452242140293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17623 < q → q < 17627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17627).mp (by decide +kernel))) hgap
  have hprev := s2L_2025
  have hrat : ((452242140293 : ℚ) / 1000000000000) ≤ ((18089685483 : ℚ) / 40000000000) + (17627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242140293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089685483 : ℚ) / 40000000000) : ℚ) : ℝ) + ((17627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17627:ℚ)^(-2:ℤ) : ℝ) = ((17627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2027 : ((((904484287 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17627 < q → q < 17657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17657).mp (by decide +kernel))) hgap
  have hprev := s2L_2026
  have hrat : ((904484287 : ℚ) / 2000000000) ≤ ((452242140293 : ℚ) / 1000000000000) + (17657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904484287 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((452242140293 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17657:ℚ)^(-2:ℤ) : ℝ) = ((17657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2028 : ((((226121073353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17657 < q → q < 17659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17659).mp (by decide +kernel))) hgap
  have hprev := s2L_2027
  have hrat : ((226121073353 : ℚ) / 500000000000) ≤ ((904484287 : ℚ) / 2000000000) + (17659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121073353 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((904484287 : ℚ) / 2000000000) : ℚ) : ℝ) + ((17659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17659:ℚ)^(-2:ℤ) : ℝ) = ((17659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2029 : ((((452242149909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17659 < q → q < 17669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17669).mp (by decide +kernel))) hgap
  have hprev := s2L_2028
  have hrat : ((452242149909 : ℚ) / 1000000000000) ≤ ((226121073353 : ℚ) / 500000000000) + (17669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242149909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121073353 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17669:ℚ)^(-2:ℤ) : ℝ) = ((17669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2030 : ((((452242153107 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17669 < q → q < 17681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17681).mp (by decide +kernel))) hgap
  have hprev := s2L_2029
  have hrat : ((452242153107 : ℚ) / 1000000000000) ≤ ((452242149909 : ℚ) / 1000000000000) + (17681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242153107 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242149909 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17681:ℚ)^(-2:ℤ) : ℝ) = ((17681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2031 : ((((90448431261 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17681 < q → q < 17683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17683).mp (by decide +kernel))) hgap
  have hprev := s2L_2030
  have hrat : ((90448431261 : ℚ) / 200000000000) ≤ ((452242153107 : ℚ) / 1000000000000) + (17683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448431261 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242153107 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17683:ℚ)^(-2:ℤ) : ℝ) = ((17683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2032 : ((((226121079747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17707, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17683 < q → q < 17707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17707).mp (by decide +kernel))) hgap
  have hprev := s2L_2031
  have hrat : ((226121079747 : ℚ) / 500000000000) ≤ ((90448431261 : ℚ) / 200000000000) + (17707:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121079747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448431261 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17707:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17707:ℚ)^(-2:ℤ) : ℝ) = ((17707:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2033 : ((((452242162681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17707 < q → q < 17713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17713).mp (by decide +kernel))) hgap
  have hprev := s2L_2032
  have hrat : ((452242162681 : ℚ) / 1000000000000) ≤ ((226121079747 : ℚ) / 500000000000) + (17713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242162681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121079747 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17713:ℚ)^(-2:ℤ) : ℝ) = ((17713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2034 : ((((226121082931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17713 < q → q < 17729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17729).mp (by decide +kernel))) hgap
  have hprev := s2L_2033
  have hrat : ((226121082931 : ℚ) / 500000000000) ≤ ((452242162681 : ℚ) / 1000000000000) + (17729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121082931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242162681 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17729:ℚ)^(-2:ℤ) : ℝ) = ((17729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2035 : ((((5653027113 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17729 < q → q < 17737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17737).mp (by decide +kernel))) hgap
  have hprev := s2L_2034
  have hrat : ((5653027113 : ℚ) / 12500000000) ≤ ((226121082931 : ℚ) / 500000000000) + (17737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653027113 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((226121082931 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17737:ℚ)^(-2:ℤ) : ℝ) = ((17737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2036 : ((((90448434443 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17737 < q → q < 17747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17747).mp (by decide +kernel))) hgap
  have hprev := s2L_2035
  have hrat : ((90448434443 : ℚ) / 200000000000) ≤ ((5653027113 : ℚ) / 12500000000) + (17747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448434443 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5653027113 : ℚ) / 12500000000) : ℚ) : ℝ) + ((17747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17747:ℚ)^(-2:ℤ) : ℝ) = ((17747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2037 : ((((452242175389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17747 < q → q < 17749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17749).mp (by decide +kernel))) hgap
  have hprev := s2L_2036
  have hrat : ((452242175389 : ℚ) / 1000000000000) ≤ ((90448434443 : ℚ) / 200000000000) + (17749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242175389 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448434443 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17749:ℚ)^(-2:ℤ) : ℝ) = ((17749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2038 : ((((452242178559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17749 < q → q < 17761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17761).mp (by decide +kernel))) hgap
  have hprev := s2L_2037
  have hrat : ((452242178559 : ℚ) / 1000000000000) ≤ ((452242175389 : ℚ) / 1000000000000) + (17761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242178559 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242175389 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17761:ℚ)^(-2:ℤ) : ℝ) = ((17761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2039 : ((((452242181721 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17761 < q → q < 17783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17783).mp (by decide +kernel))) hgap
  have hprev := s2L_2038
  have hrat : ((452242181721 : ℚ) / 1000000000000) ≤ ((452242178559 : ℚ) / 1000000000000) + (17783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242181721 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242178559 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17783:ℚ)^(-2:ℤ) : ℝ) = ((17783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2040 : ((((452242184881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17783 < q → q < 17789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17789).mp (by decide +kernel))) hgap
  have hprev := s2L_2039
  have hrat : ((452242184881 : ℚ) / 1000000000000) ≤ ((452242181721 : ℚ) / 1000000000000) + (17789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242184881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242181721 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17789:ℚ)^(-2:ℤ) : ℝ) = ((17789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2041 : ((((11306054701 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17789 < q → q < 17791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17791).mp (by decide +kernel))) hgap
  have hprev := s2L_2040
  have hrat : ((11306054701 : ℚ) / 25000000000) ≤ ((452242184881 : ℚ) / 1000000000000) + (17791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306054701 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452242184881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17791:ℚ)^(-2:ℤ) : ℝ) = ((17791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2042 : ((((452242191193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17791 < q → q < 17807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17807).mp (by decide +kernel))) hgap
  have hprev := s2L_2041
  have hrat : ((452242191193 : ℚ) / 1000000000000) ≤ ((11306054701 : ℚ) / 25000000000) + (17807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242191193 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306054701 : ℚ) / 25000000000) : ℚ) : ℝ) + ((17807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17807:ℚ)^(-2:ℤ) : ℝ) = ((17807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2043 : ((((452242194339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17807 < q → q < 17827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17827).mp (by decide +kernel))) hgap
  have hprev := s2L_2042
  have hrat : ((452242194339 : ℚ) / 1000000000000) ≤ ((452242191193 : ℚ) / 1000000000000) + (17827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242194339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242191193 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17827:ℚ)^(-2:ℤ) : ℝ) = ((17827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2044 : ((((226121098741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17827 < q → q < 17837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17837).mp (by decide +kernel))) hgap
  have hprev := s2L_2043
  have hrat : ((226121098741 : ℚ) / 500000000000) ≤ ((452242194339 : ℚ) / 1000000000000) + (17837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121098741 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242194339 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17837:ℚ)^(-2:ℤ) : ℝ) = ((17837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2045 : ((((28265137539 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17837 < q → q < 17839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17839).mp (by decide +kernel))) hgap
  have hprev := s2L_2044
  have hrat : ((28265137539 : ℚ) / 62500000000) ≤ ((226121098741 : ℚ) / 500000000000) + (17839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265137539 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121098741 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17839:ℚ)^(-2:ℤ) : ℝ) = ((17839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2046 : ((((226121101881 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17839 < q → q < 17851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17851).mp (by decide +kernel))) hgap
  have hprev := s2L_2045
  have hrat : ((226121101881 : ℚ) / 500000000000) ≤ ((28265137539 : ℚ) / 62500000000) + (17851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121101881 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265137539 : ℚ) / 62500000000) : ℚ) : ℝ) + ((17851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17851:ℚ)^(-2:ℤ) : ℝ) = ((17851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2047 : ((((90448441379 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17851 < q → q < 17863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17863).mp (by decide +kernel))) hgap
  have hprev := s2L_2046
  have hrat : ((90448441379 : ℚ) / 200000000000) ≤ ((226121101881 : ℚ) / 500000000000) + (17863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448441379 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121101881 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17863:ℚ)^(-2:ℤ) : ℝ) = ((17863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2048 : ((((226121105011 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17863 < q → q < 17881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17881).mp (by decide +kernel))) hgap
  have hprev := s2L_2047
  have hrat : ((226121105011 : ℚ) / 500000000000) ≤ ((90448441379 : ℚ) / 200000000000) + (17881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121105011 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448441379 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17881:ℚ)^(-2:ℤ) : ℝ) = ((17881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2049 : ((((226121106573 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17891, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17881 < q → q < 17891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17891).mp (by decide +kernel))) hgap
  have hprev := s2L_2048
  have hrat : ((226121106573 : ℚ) / 500000000000) ≤ ((226121105011 : ℚ) / 500000000000) + (17891:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121106573 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121105011 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17891:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17891:ℚ)^(-2:ℤ) : ℝ) = ((17891:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2050 : ((((90448443253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17891 < q → q < 17903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17903).mp (by decide +kernel))) hgap
  have hprev := s2L_2049
  have hrat : ((90448443253 : ℚ) / 200000000000) ≤ ((226121106573 : ℚ) / 500000000000) + (17903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448443253 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121106573 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17903:ℚ)^(-2:ℤ) : ℝ) = ((17903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2051 : ((((226121109691 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17903 < q → q < 17909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17909).mp (by decide +kernel))) hgap
  have hprev := s2L_2050
  have hrat : ((226121109691 : ℚ) / 500000000000) ≤ ((90448443253 : ℚ) / 200000000000) + (17909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121109691 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448443253 : ℚ) / 200000000000) : ℚ) : ℝ) + ((17909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17909:ℚ)^(-2:ℤ) : ℝ) = ((17909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2052 : ((((452242222499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17909 < q → q < 17911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17911).mp (by decide +kernel))) hgap
  have hprev := s2L_2051
  have hrat : ((452242222499 : ℚ) / 1000000000000) ≤ ((226121109691 : ℚ) / 500000000000) + (17911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242222499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121109691 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17911:ℚ)^(-2:ℤ) : ℝ) = ((17911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2053 : ((((113060556403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17911 < q → q < 17921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17921).mp (by decide +kernel))) hgap
  have hprev := s2L_2052
  have hrat : ((113060556403 : ℚ) / 250000000000) ≤ ((452242222499 : ℚ) / 1000000000000) + (17921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060556403 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242222499 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17921:ℚ)^(-2:ℤ) : ℝ) = ((17921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2054 : ((((113060557181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17921 < q → q < 17923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17923).mp (by decide +kernel))) hgap
  have hprev := s2L_2053
  have hrat : ((113060557181 : ℚ) / 250000000000) ≤ ((113060556403 : ℚ) / 250000000000) + (17923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060557181 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060556403 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17923:ℚ)^(-2:ℤ) : ℝ) = ((17923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2055 : ((((226121115917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17923 < q → q < 17929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17929).mp (by decide +kernel))) hgap
  have hprev := s2L_2054
  have hrat : ((226121115917 : ℚ) / 500000000000) ≤ ((113060557181 : ℚ) / 250000000000) + (17929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121115917 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060557181 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17929:ℚ)^(-2:ℤ) : ℝ) = ((17929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2056 : ((((452242234941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17929 < q → q < 17939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17939).mp (by decide +kernel))) hgap
  have hprev := s2L_2055
  have hrat : ((452242234941 : ℚ) / 1000000000000) ≤ ((226121115917 : ℚ) / 500000000000) + (17939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242234941 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121115917 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17939:ℚ)^(-2:ℤ) : ℝ) = ((17939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2057 : ((((226121119021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17939 < q → q < 17957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17957).mp (by decide +kernel))) hgap
  have hprev := s2L_2056
  have hrat : ((226121119021 : ℚ) / 500000000000) ≤ ((452242234941 : ℚ) / 1000000000000) + (17957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121119021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242234941 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((17957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17957:ℚ)^(-2:ℤ) : ℝ) = ((17957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2058 : ((((226121120571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17957 < q → q < 17959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17959).mp (by decide +kernel))) hgap
  have hprev := s2L_2057
  have hrat : ((226121120571 : ℚ) / 500000000000) ≤ ((226121119021 : ℚ) / 500000000000) + (17959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121120571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121119021 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17959:ℚ)^(-2:ℤ) : ℝ) = ((17959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2059 : ((((226121122119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17959 < q → q < 17971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17971).mp (by decide +kernel))) hgap
  have hprev := s2L_2058
  have hrat : ((226121122119 : ℚ) / 500000000000) ≤ ((226121120571 : ℚ) / 500000000000) + (17971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121122119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121120571 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17971:ℚ)^(-2:ℤ) : ℝ) = ((17971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2060 : ((((113060561833 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17971 < q → q < 17977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17977).mp (by decide +kernel))) hgap
  have hprev := s2L_2059
  have hrat : ((113060561833 : ℚ) / 250000000000) ≤ ((226121122119 : ℚ) / 500000000000) + (17977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060561833 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121122119 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17977:ℚ)^(-2:ℤ) : ℝ) = ((17977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2061 : ((((56530281303 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17977 < q → q < 17981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17981).mp (by decide +kernel))) hgap
  have hprev := s2L_2060
  have hrat : ((56530281303 : ℚ) / 125000000000) ≤ ((113060561833 : ℚ) / 250000000000) + (17981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530281303 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060561833 : ℚ) / 250000000000) : ℚ) : ℝ) + ((17981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17981:ℚ)^(-2:ℤ) : ℝ) = ((17981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2062 : ((((226121126757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17981 < q → q < 17987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17987).mp (by decide +kernel))) hgap
  have hprev := s2L_2061
  have hrat : ((226121126757 : ℚ) / 500000000000) ≤ ((56530281303 : ℚ) / 125000000000) + (17987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121126757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530281303 : ℚ) / 125000000000) : ℚ) : ℝ) + ((17987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17987:ℚ)^(-2:ℤ) : ℝ) = ((17987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2063 : ((((113060564151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 17989, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17987 < q → q < 17989 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 17989).mp (by decide +kernel))) hgap
  have hprev := s2L_2062
  have hrat : ((113060564151 : ℚ) / 250000000000) ≤ ((226121126757 : ℚ) / 500000000000) + (17989:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060564151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121126757 : ℚ) / 500000000000) : ℚ) : ℝ) + ((17989:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((17989:ℚ)^(-2:ℤ) : ℝ) = ((17989:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2064 : ((((90448451937 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 17989 < q → q < 18013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18013).mp (by decide +kernel))) hgap
  have hprev := s2L_2063
  have hrat : ((90448451937 : ℚ) / 200000000000) ≤ ((113060564151 : ℚ) / 250000000000) + (18013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448451937 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060564151 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18013:ℚ)^(-2:ℤ) : ℝ) = ((18013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2065 : ((((452242262757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18013 < q → q < 18041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18041).mp (by decide +kernel))) hgap
  have hprev := s2L_2064
  have hrat : ((452242262757 : ℚ) / 1000000000000) ≤ ((90448451937 : ℚ) / 200000000000) + (18041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242262757 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448451937 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18041:ℚ)^(-2:ℤ) : ℝ) = ((18041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2066 : ((((113060566457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18041 < q → q < 18043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18043).mp (by decide +kernel))) hgap
  have hprev := s2L_2065
  have hrat : ((113060566457 : ℚ) / 250000000000) ≤ ((452242262757 : ℚ) / 1000000000000) + (18043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060566457 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242262757 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18043:ℚ)^(-2:ℤ) : ℝ) = ((18043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2067 : ((((226121134449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18043 < q → q < 18047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18047).mp (by decide +kernel))) hgap
  have hprev := s2L_2066
  have hrat : ((226121134449 : ℚ) / 500000000000) ≤ ((113060566457 : ℚ) / 250000000000) + (18047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121134449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060566457 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18047:ℚ)^(-2:ℤ) : ℝ) = ((18047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2068 : ((((452242271967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18047 < q → q < 18049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18049).mp (by decide +kernel))) hgap
  have hprev := s2L_2067
  have hrat : ((452242271967 : ℚ) / 1000000000000) ≤ ((226121134449 : ℚ) / 500000000000) + (18049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242271967 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121134449 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18049:ℚ)^(-2:ℤ) : ℝ) = ((18049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2069 : ((((452242275033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18049 < q → q < 18059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18059).mp (by decide +kernel))) hgap
  have hprev := s2L_2068
  have hrat : ((452242275033 : ℚ) / 1000000000000) ≤ ((452242271967 : ℚ) / 1000000000000) + (18059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242275033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242271967 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18059:ℚ)^(-2:ℤ) : ℝ) = ((18059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2070 : ((((226121139049 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18059 < q → q < 18061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18061).mp (by decide +kernel))) hgap
  have hprev := s2L_2069
  have hrat : ((226121139049 : ℚ) / 500000000000) ≤ ((452242275033 : ℚ) / 1000000000000) + (18061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121139049 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242275033 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18061:ℚ)^(-2:ℤ) : ℝ) = ((18061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2071 : ((((226121140579 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18077, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18061 < q → q < 18077 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18077).mp (by decide +kernel))) hgap
  have hprev := s2L_2070
  have hrat : ((226121140579 : ℚ) / 500000000000) ≤ ((226121139049 : ℚ) / 500000000000) + (18077:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121140579 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121139049 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18077:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18077:ℚ)^(-2:ℤ) : ℝ) = ((18077:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2072 : ((((226121142107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18077 < q → q < 18089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18089).mp (by decide +kernel))) hgap
  have hprev := s2L_2071
  have hrat : ((226121142107 : ℚ) / 500000000000) ≤ ((226121140579 : ℚ) / 500000000000) + (18089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121142107 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121140579 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18089:ℚ)^(-2:ℤ) : ℝ) = ((18089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2073 : ((((452242287267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18089 < q → q < 18097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18097).mp (by decide +kernel))) hgap
  have hprev := s2L_2072
  have hrat : ((452242287267 : ℚ) / 1000000000000) ≤ ((226121142107 : ℚ) / 500000000000) + (18097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242287267 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121142107 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18097:ℚ)^(-2:ℤ) : ℝ) = ((18097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2074 : ((((452242290313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18097 < q → q < 18119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18119).mp (by decide +kernel))) hgap
  have hprev := s2L_2073
  have hrat : ((452242290313 : ℚ) / 1000000000000) ≤ ((452242287267 : ℚ) / 1000000000000) + (18119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242290313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242287267 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18119:ℚ)^(-2:ℤ) : ℝ) = ((18119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2075 : ((((226121146679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18119 < q → q < 18121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18121).mp (by decide +kernel))) hgap
  have hprev := s2L_2074
  have hrat : ((226121146679 : ℚ) / 500000000000) ≤ ((452242290313 : ℚ) / 1000000000000) + (18121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121146679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242290313 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18121:ℚ)^(-2:ℤ) : ℝ) = ((18121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2076 : ((((452242296401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18121 < q → q < 18127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18127).mp (by decide +kernel))) hgap
  have hprev := s2L_2075
  have hrat : ((452242296401 : ℚ) / 1000000000000) ≤ ((226121146679 : ℚ) / 500000000000) + (18127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242296401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121146679 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18127:ℚ)^(-2:ℤ) : ℝ) = ((18127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2077 : ((((226121149721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18127 < q → q < 18131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18131).mp (by decide +kernel))) hgap
  have hprev := s2L_2076
  have hrat : ((226121149721 : ℚ) / 500000000000) ≤ ((452242296401 : ℚ) / 1000000000000) + (18131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121149721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242296401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18131:ℚ)^(-2:ℤ) : ℝ) = ((18131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2078 : ((((452242302483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18131 < q → q < 18133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18133).mp (by decide +kernel))) hgap
  have hprev := s2L_2077
  have hrat : ((452242302483 : ℚ) / 1000000000000) ≤ ((226121149721 : ℚ) / 500000000000) + (18133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242302483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121149721 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18133:ℚ)^(-2:ℤ) : ℝ) = ((18133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2079 : ((((5653028819 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18133 < q → q < 18143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18143).mp (by decide +kernel))) hgap
  have hprev := s2L_2078
  have hrat : ((5653028819 : ℚ) / 12500000000) ≤ ((452242302483 : ℚ) / 1000000000000) + (18143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5653028819 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((452242302483 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18143:ℚ)^(-2:ℤ) : ℝ) = ((18143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2080 : ((((90448461711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18143 < q → q < 18149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18149).mp (by decide +kernel))) hgap
  have hprev := s2L_2079
  have hrat : ((90448461711 : ℚ) / 200000000000) ≤ ((5653028819 : ℚ) / 12500000000) + (18149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448461711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((5653028819 : ℚ) / 12500000000) : ℚ) : ℝ) + ((18149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18149:ℚ)^(-2:ℤ) : ℝ) = ((18149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2081 : ((((14132572237 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18149 < q → q < 18169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18169).mp (by decide +kernel))) hgap
  have hprev := s2L_2080
  have hrat : ((14132572237 : ℚ) / 31250000000) ≤ ((90448461711 : ℚ) / 200000000000) + (18169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132572237 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((90448461711 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18169:ℚ)^(-2:ℤ) : ℝ) = ((18169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2082 : ((((452242314609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18169 < q → q < 18181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18181).mp (by decide +kernel))) hgap
  have hprev := s2L_2081
  have hrat : ((452242314609 : ℚ) / 1000000000000) ≤ ((14132572237 : ℚ) / 31250000000) + (18181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242314609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132572237 : ℚ) / 31250000000) : ℚ) : ℝ) + ((18181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18181:ℚ)^(-2:ℤ) : ℝ) = ((18181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2083 : ((((45224231763 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18181 < q → q < 18191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18191).mp (by decide +kernel))) hgap
  have hprev := s2L_2082
  have hrat : ((45224231763 : ℚ) / 100000000000) ≤ ((452242314609 : ℚ) / 1000000000000) + (18191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224231763 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242314609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18191:ℚ)^(-2:ℤ) : ℝ) = ((18191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2084 : ((((452242320649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18199, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18191 < q → q < 18199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18199).mp (by decide +kernel))) hgap
  have hprev := s2L_2083
  have hrat : ((452242320649 : ℚ) / 1000000000000) ≤ ((45224231763 : ℚ) / 100000000000) + (18199:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242320649 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224231763 : ℚ) / 100000000000) : ℚ) : ℝ) + ((18199:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18199:ℚ)^(-2:ℤ) : ℝ) = ((18199:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2085 : ((((28265145229 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18199 < q → q < 18211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18211).mp (by decide +kernel))) hgap
  have hprev := s2L_2084
  have hrat : ((28265145229 : ℚ) / 62500000000) ≤ ((452242320649 : ℚ) / 1000000000000) + (18211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265145229 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242320649 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18211:ℚ)^(-2:ℤ) : ℝ) = ((18211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2086 : ((((452242326677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18211 < q → q < 18217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18217).mp (by decide +kernel))) hgap
  have hprev := s2L_2085
  have hrat : ((452242326677 : ℚ) / 1000000000000) ≤ ((28265145229 : ℚ) / 62500000000) + (18217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242326677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265145229 : ℚ) / 62500000000) : ℚ) : ℝ) + ((18217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18217:ℚ)^(-2:ℤ) : ℝ) = ((18217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2087 : ((((56530291211 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18217 < q → q < 18223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18223).mp (by decide +kernel))) hgap
  have hprev := s2L_2086
  have hrat : ((56530291211 : ℚ) / 125000000000) ≤ ((452242326677 : ℚ) / 1000000000000) + (18223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530291211 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242326677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18223:ℚ)^(-2:ℤ) : ℝ) = ((18223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2088 : ((((452242332697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18223 < q → q < 18229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18229).mp (by decide +kernel))) hgap
  have hprev := s2L_2087
  have hrat : ((452242332697 : ℚ) / 1000000000000) ≤ ((56530291211 : ℚ) / 125000000000) + (18229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242332697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530291211 : ℚ) / 125000000000) : ℚ) : ℝ) + ((18229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18229:ℚ)^(-2:ℤ) : ℝ) = ((18229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2089 : ((((90448467141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18229 < q → q < 18233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18233).mp (by decide +kernel))) hgap
  have hprev := s2L_2088
  have hrat : ((90448467141 : ℚ) / 200000000000) ≤ ((452242332697 : ℚ) / 1000000000000) + (18233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448467141 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242332697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18233:ℚ)^(-2:ℤ) : ℝ) = ((18233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2090 : ((((452242338707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18233 < q → q < 18251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18251).mp (by decide +kernel))) hgap
  have hprev := s2L_2089
  have hrat : ((452242338707 : ℚ) / 1000000000000) ≤ ((90448467141 : ℚ) / 200000000000) + (18251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242338707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448467141 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18251:ℚ)^(-2:ℤ) : ℝ) = ((18251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2091 : ((((113060585427 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18251 < q → q < 18253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18253).mp (by decide +kernel))) hgap
  have hprev := s2L_2090
  have hrat : ((113060585427 : ℚ) / 250000000000) ≤ ((452242338707 : ℚ) / 1000000000000) + (18253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060585427 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242338707 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18253:ℚ)^(-2:ℤ) : ℝ) = ((18253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2092 : ((((113060586177 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18253 < q → q < 18257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18257).mp (by decide +kernel))) hgap
  have hprev := s2L_2091
  have hrat : ((113060586177 : ℚ) / 250000000000) ≤ ((113060585427 : ℚ) / 250000000000) + (18257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060586177 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060585427 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18257:ℚ)^(-2:ℤ) : ℝ) = ((18257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2093 : ((((56530293463 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18257 < q → q < 18269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18269).mp (by decide +kernel))) hgap
  have hprev := s2L_2092
  have hrat : ((56530293463 : ℚ) / 125000000000) ≤ ((113060586177 : ℚ) / 250000000000) + (18269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530293463 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060586177 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18269:ℚ)^(-2:ℤ) : ℝ) = ((18269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2094 : ((((226121175347 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18269 < q → q < 18287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18287).mp (by decide +kernel))) hgap
  have hprev := s2L_2093
  have hrat : ((226121175347 : ℚ) / 500000000000) ≤ ((56530293463 : ℚ) / 125000000000) + (18287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121175347 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530293463 : ℚ) / 125000000000) : ℚ) : ℝ) + ((18287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18287:ℚ)^(-2:ℤ) : ℝ) = ((18287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2095 : ((((452242353683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18287 < q → q < 18289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18289).mp (by decide +kernel))) hgap
  have hprev := s2L_2094
  have hrat : ((452242353683 : ℚ) / 1000000000000) ≤ ((226121175347 : ℚ) / 500000000000) + (18289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242353683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121175347 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18289:ℚ)^(-2:ℤ) : ℝ) = ((18289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2096 : ((((113060589167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18289 < q → q < 18301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18301).mp (by decide +kernel))) hgap
  have hprev := s2L_2095
  have hrat : ((113060589167 : ℚ) / 250000000000) ≤ ((452242353683 : ℚ) / 1000000000000) + (18301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060589167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242353683 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18301:ℚ)^(-2:ℤ) : ℝ) = ((18301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2097 : ((((452242359651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18301 < q → q < 18307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18307).mp (by decide +kernel))) hgap
  have hprev := s2L_2096
  have hrat : ((452242359651 : ℚ) / 1000000000000) ≤ ((113060589167 : ℚ) / 250000000000) + (18307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242359651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060589167 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18307:ℚ)^(-2:ℤ) : ℝ) = ((18307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2098 : ((((452242362633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18307 < q → q < 18311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18311).mp (by decide +kernel))) hgap
  have hprev := s2L_2097
  have hrat : ((452242362633 : ℚ) / 1000000000000) ≤ ((452242359651 : ℚ) / 1000000000000) + (18311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242362633 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242359651 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18311:ℚ)^(-2:ℤ) : ℝ) = ((18311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2099 : ((((226121182807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18311 < q → q < 18313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18313).mp (by decide +kernel))) hgap
  have hprev := s2L_2098
  have hrat : ((226121182807 : ℚ) / 500000000000) ≤ ((452242362633 : ℚ) / 1000000000000) + (18313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121182807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242362633 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18313:ℚ)^(-2:ℤ) : ℝ) = ((18313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2100 : ((((45224236859 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18313 < q → q < 18329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18329).mp (by decide +kernel))) hgap
  have hprev := s2L_2099
  have hrat : ((45224236859 : ℚ) / 100000000000) ≤ ((226121182807 : ℚ) / 500000000000) + (18329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224236859 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121182807 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18329:ℚ)^(-2:ℤ) : ℝ) = ((18329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2101 : ((((226121185781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18329 < q → q < 18341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18341).mp (by decide +kernel))) hgap
  have hprev := s2L_2100
  have hrat : ((226121185781 : ℚ) / 500000000000) ≤ ((45224236859 : ℚ) / 100000000000) + (18341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121185781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224236859 : ℚ) / 100000000000) : ℚ) : ℝ) + ((18341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18341:ℚ)^(-2:ℤ) : ℝ) = ((18341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2102 : ((((45224237453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18341 < q → q < 18353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18353).mp (by decide +kernel))) hgap
  have hprev := s2L_2101
  have hrat : ((45224237453 : ℚ) / 100000000000) ≤ ((226121185781 : ℚ) / 500000000000) + (18353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224237453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121185781 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18353:ℚ)^(-2:ℤ) : ℝ) = ((18353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2103 : ((((226121188747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18353 < q → q < 18367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18367).mp (by decide +kernel))) hgap
  have hprev := s2L_2102
  have hrat : ((226121188747 : ℚ) / 500000000000) ≤ ((45224237453 : ℚ) / 100000000000) + (18367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121188747 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224237453 : ℚ) / 100000000000) : ℚ) : ℝ) + ((18367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18367:ℚ)^(-2:ℤ) : ℝ) = ((18367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2104 : ((((452242380457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18367 < q → q < 18371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18371).mp (by decide +kernel))) hgap
  have hprev := s2L_2103
  have hrat : ((452242380457 : ℚ) / 1000000000000) ≤ ((226121188747 : ℚ) / 500000000000) + (18371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242380457 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121188747 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18371:ℚ)^(-2:ℤ) : ℝ) = ((18371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2105 : ((((452242383417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18371 < q → q < 18379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18379).mp (by decide +kernel))) hgap
  have hprev := s2L_2104
  have hrat : ((452242383417 : ℚ) / 1000000000000) ≤ ((452242380457 : ℚ) / 1000000000000) + (18379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242383417 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242380457 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18379:ℚ)^(-2:ℤ) : ℝ) = ((18379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2106 : ((((452242386371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18379 < q → q < 18397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18397).mp (by decide +kernel))) hgap
  have hprev := s2L_2105
  have hrat : ((452242386371 : ℚ) / 1000000000000) ≤ ((452242383417 : ℚ) / 1000000000000) + (18397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242386371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242383417 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18397:ℚ)^(-2:ℤ) : ℝ) = ((18397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2107 : ((((113060597331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18397 < q → q < 18401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18401).mp (by decide +kernel))) hgap
  have hprev := s2L_2106
  have hrat : ((113060597331 : ℚ) / 250000000000) ≤ ((452242386371 : ℚ) / 1000000000000) + (18401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060597331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242386371 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18401:ℚ)^(-2:ℤ) : ℝ) = ((18401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2108 : ((((452242392273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18401 < q → q < 18413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18413).mp (by decide +kernel))) hgap
  have hprev := s2L_2107
  have hrat : ((452242392273 : ℚ) / 1000000000000) ≤ ((113060597331 : ℚ) / 250000000000) + (18413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242392273 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060597331 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18413:ℚ)^(-2:ℤ) : ℝ) = ((18413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2109 : ((((226121197609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18413 < q → q < 18427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18427).mp (by decide +kernel))) hgap
  have hprev := s2L_2108
  have hrat : ((226121197609 : ℚ) / 500000000000) ≤ ((452242392273 : ℚ) / 1000000000000) + (18427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121197609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242392273 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18427:ℚ)^(-2:ℤ) : ℝ) = ((18427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2110 : ((((452242398161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18427 < q → q < 18433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18433).mp (by decide +kernel))) hgap
  have hprev := s2L_2109
  have hrat : ((452242398161 : ℚ) / 1000000000000) ≤ ((226121197609 : ℚ) / 500000000000) + (18433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242398161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121197609 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18433:ℚ)^(-2:ℤ) : ℝ) = ((18433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2111 : ((((226121200551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18433 < q → q < 18439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18439).mp (by decide +kernel))) hgap
  have hprev := s2L_2110
  have hrat : ((226121200551 : ℚ) / 500000000000) ≤ ((452242398161 : ℚ) / 1000000000000) + (18439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121200551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242398161 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18439:ℚ)^(-2:ℤ) : ℝ) = ((18439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2112 : ((((452242404041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18439 < q → q < 18443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18443).mp (by decide +kernel))) hgap
  have hprev := s2L_2111
  have hrat : ((452242404041 : ℚ) / 1000000000000) ≤ ((226121200551 : ℚ) / 500000000000) + (18443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242404041 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121200551 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18443:ℚ)^(-2:ℤ) : ℝ) = ((18443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2113 : ((((226121203489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18443 < q → q < 18451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18451).mp (by decide +kernel))) hgap
  have hprev := s2L_2112
  have hrat : ((226121203489 : ℚ) / 500000000000) ≤ ((452242404041 : ℚ) / 1000000000000) + (18451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121203489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242404041 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18451:ℚ)^(-2:ℤ) : ℝ) = ((18451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2114 : ((((452242409913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18451 < q → q < 18457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18457).mp (by decide +kernel))) hgap
  have hprev := s2L_2113
  have hrat : ((452242409913 : ℚ) / 1000000000000) ≤ ((226121203489 : ℚ) / 500000000000) + (18457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242409913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121203489 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18457:ℚ)^(-2:ℤ) : ℝ) = ((18457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2115 : ((((452242412847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18457 < q → q < 18461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18461).mp (by decide +kernel))) hgap
  have hprev := s2L_2114
  have hrat : ((452242412847 : ℚ) / 1000000000000) ≤ ((452242409913 : ℚ) / 1000000000000) + (18461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242412847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242409913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18461:ℚ)^(-2:ℤ) : ℝ) = ((18461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2116 : ((((226121207887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18461 < q → q < 18481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18481).mp (by decide +kernel))) hgap
  have hprev := s2L_2115
  have hrat : ((226121207887 : ℚ) / 500000000000) ≤ ((452242412847 : ℚ) / 1000000000000) + (18481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121207887 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242412847 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18481:ℚ)^(-2:ℤ) : ℝ) = ((18481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2117 : ((((226121209349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18481 < q → q < 18493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18493).mp (by decide +kernel))) hgap
  have hprev := s2L_2116
  have hrat : ((226121209349 : ℚ) / 500000000000) ≤ ((226121207887 : ℚ) / 500000000000) + (18493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121209349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121207887 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18493:ℚ)^(-2:ℤ) : ℝ) = ((18493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2118 : ((((226121210809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18493 < q → q < 18503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18503).mp (by decide +kernel))) hgap
  have hprev := s2L_2117
  have hrat : ((226121210809 : ℚ) / 500000000000) ≤ ((226121209349 : ℚ) / 500000000000) + (18503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121210809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121209349 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18503:ℚ)^(-2:ℤ) : ℝ) = ((18503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2119 : ((((226121212267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18503 < q → q < 18517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18517).mp (by decide +kernel))) hgap
  have hprev := s2L_2118
  have hrat : ((226121212267 : ℚ) / 500000000000) ≤ ((226121210809 : ℚ) / 500000000000) + (18517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121212267 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121210809 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18517:ℚ)^(-2:ℤ) : ℝ) = ((18517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2120 : ((((452242427449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18517 < q → q < 18521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18521).mp (by decide +kernel))) hgap
  have hprev := s2L_2119
  have hrat : ((452242427449 : ℚ) / 1000000000000) ≤ ((226121212267 : ℚ) / 500000000000) + (18521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242427449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121212267 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18521:ℚ)^(-2:ℤ) : ℝ) = ((18521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2121 : ((((452242430363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18521 < q → q < 18523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18523).mp (by decide +kernel))) hgap
  have hprev := s2L_2120
  have hrat : ((452242430363 : ℚ) / 1000000000000) ≤ ((452242427449 : ℚ) / 1000000000000) + (18523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242430363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242427449 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18523:ℚ)^(-2:ℤ) : ℝ) = ((18523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2122 : ((((56530304159 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18523 < q → q < 18539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18539).mp (by decide +kernel))) hgap
  have hprev := s2L_2121
  have hrat : ((56530304159 : ℚ) / 125000000000) ≤ ((452242430363 : ℚ) / 1000000000000) + (18539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530304159 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242430363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18539:ℚ)^(-2:ℤ) : ℝ) = ((18539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2123 : ((((22612121809 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18539 < q → q < 18541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18541).mp (by decide +kernel))) hgap
  have hprev := s2L_2122
  have hrat : ((22612121809 : ℚ) / 50000000000) ≤ ((56530304159 : ℚ) / 125000000000) + (18541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612121809 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56530304159 : ℚ) / 125000000000) : ℚ) : ℝ) + ((18541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18541:ℚ)^(-2:ℤ) : ℝ) = ((18541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2124 : ((((90448487817 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18541 < q → q < 18553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18553).mp (by decide +kernel))) hgap
  have hprev := s2L_2123
  have hrat : ((90448487817 : ℚ) / 200000000000) ≤ ((22612121809 : ℚ) / 50000000000) + (18553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448487817 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612121809 : ℚ) / 50000000000) : ℚ) : ℝ) + ((18553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18553:ℚ)^(-2:ℤ) : ℝ) = ((18553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2125 : ((((22612122099 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18553 < q → q < 18583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18583).mp (by decide +kernel))) hgap
  have hprev := s2L_2124
  have hrat : ((22612122099 : ℚ) / 50000000000) ≤ ((90448487817 : ℚ) / 200000000000) + (18583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612122099 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((90448487817 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18583:ℚ)^(-2:ℤ) : ℝ) = ((18583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2126 : ((((226121222437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18583 < q → q < 18587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18587).mp (by decide +kernel))) hgap
  have hprev := s2L_2125
  have hrat : ((226121222437 : ℚ) / 500000000000) ≤ ((22612122099 : ℚ) / 50000000000) + (18587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121222437 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612122099 : ℚ) / 50000000000) : ℚ) : ℝ) + ((18587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18587:ℚ)^(-2:ℤ) : ℝ) = ((18587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2127 : ((((226121223883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18587 < q → q < 18593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18593).mp (by decide +kernel))) hgap
  have hprev := s2L_2126
  have hrat : ((226121223883 : ℚ) / 500000000000) ≤ ((226121222437 : ℚ) / 500000000000) + (18593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121223883 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121222437 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18593:ℚ)^(-2:ℤ) : ℝ) = ((18593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2128 : ((((452242450651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18593 < q → q < 18617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18617).mp (by decide +kernel))) hgap
  have hprev := s2L_2127
  have hrat : ((452242450651 : ℚ) / 1000000000000) ≤ ((226121223883 : ℚ) / 500000000000) + (18617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242450651 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121223883 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18617:ℚ)^(-2:ℤ) : ℝ) = ((18617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2129 : ((((45224245353 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18617 < q → q < 18637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18637).mp (by decide +kernel))) hgap
  have hprev := s2L_2128
  have hrat : ((45224245353 : ℚ) / 100000000000) ≤ ((452242450651 : ℚ) / 1000000000000) + (18637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224245353 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242450651 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18637:ℚ)^(-2:ℤ) : ℝ) = ((18637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2130 : ((((452242456401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18637 < q → q < 18661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18661).mp (by decide +kernel))) hgap
  have hprev := s2L_2129
  have hrat : ((452242456401 : ℚ) / 1000000000000) ≤ ((45224245353 : ℚ) / 100000000000) + (18661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242456401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224245353 : ℚ) / 100000000000) : ℚ) : ℝ) + ((18661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18661:ℚ)^(-2:ℤ) : ℝ) = ((18661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2131 : ((((452242459269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18661 < q → q < 18671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18671).mp (by decide +kernel))) hgap
  have hprev := s2L_2130
  have hrat : ((452242459269 : ℚ) / 1000000000000) ≤ ((452242456401 : ℚ) / 1000000000000) + (18671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242459269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242456401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18671:ℚ)^(-2:ℤ) : ℝ) = ((18671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2132 : ((((90448492427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18671 < q → q < 18679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18679).mp (by decide +kernel))) hgap
  have hprev := s2L_2131
  have hrat : ((90448492427 : ℚ) / 200000000000) ≤ ((452242459269 : ℚ) / 1000000000000) + (18679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448492427 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242459269 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18679:ℚ)^(-2:ℤ) : ℝ) = ((18679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2133 : ((((452242464997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18679 < q → q < 18691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18691).mp (by decide +kernel))) hgap
  have hprev := s2L_2132
  have hrat : ((452242464997 : ℚ) / 1000000000000) ≤ ((90448492427 : ℚ) / 200000000000) + (18691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242464997 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448492427 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18691:ℚ)^(-2:ℤ) : ℝ) = ((18691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2134 : ((((28265154241 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18691 < q → q < 18701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18701).mp (by decide +kernel))) hgap
  have hprev := s2L_2133
  have hrat : ((28265154241 : ℚ) / 62500000000) ≤ ((452242464997 : ℚ) / 1000000000000) + (18701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265154241 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242464997 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18701:ℚ)^(-2:ℤ) : ℝ) = ((18701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2135 : ((((452242470711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18701 < q → q < 18713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18713).mp (by decide +kernel))) hgap
  have hprev := s2L_2134
  have hrat : ((452242470711 : ℚ) / 1000000000000) ≤ ((28265154241 : ℚ) / 62500000000) + (18713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242470711 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265154241 : ℚ) / 62500000000) : ℚ) : ℝ) + ((18713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18713:ℚ)^(-2:ℤ) : ℝ) = ((18713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2136 : ((((113060618391 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18713 < q → q < 18719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18719).mp (by decide +kernel))) hgap
  have hprev := s2L_2135
  have hrat : ((113060618391 : ℚ) / 250000000000) ≤ ((452242470711 : ℚ) / 1000000000000) + (18719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060618391 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242470711 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18719:ℚ)^(-2:ℤ) : ℝ) = ((18719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2137 : ((((226121238207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18719 < q → q < 18731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18731).mp (by decide +kernel))) hgap
  have hprev := s2L_2136
  have hrat : ((226121238207 : ℚ) / 500000000000) ≤ ((113060618391 : ℚ) / 250000000000) + (18731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121238207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060618391 : ℚ) / 250000000000) : ℚ) : ℝ) + ((18731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18731:ℚ)^(-2:ℤ) : ℝ) = ((18731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2138 : ((((22612123963 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18731 < q → q < 18743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18743).mp (by decide +kernel))) hgap
  have hprev := s2L_2137
  have hrat : ((22612123963 : ℚ) / 50000000000) ≤ ((226121238207 : ℚ) / 500000000000) + (18743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612123963 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121238207 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18743:ℚ)^(-2:ℤ) : ℝ) = ((18743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2139 : ((((56530310263 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18743 < q → q < 18749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18749).mp (by decide +kernel))) hgap
  have hprev := s2L_2138
  have hrat : ((56530310263 : ℚ) / 125000000000) ≤ ((22612123963 : ℚ) / 50000000000) + (18749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530310263 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22612123963 : ℚ) / 50000000000) : ℚ) : ℝ) + ((18749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18749:ℚ)^(-2:ℤ) : ℝ) = ((18749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2140 : ((((226121242473 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18749 < q → q < 18757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18757).mp (by decide +kernel))) hgap
  have hprev := s2L_2139
  have hrat : ((226121242473 : ℚ) / 500000000000) ≤ ((56530310263 : ℚ) / 125000000000) + (18757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121242473 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56530310263 : ℚ) / 125000000000) : ℚ) : ℝ) + ((18757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18757:ℚ)^(-2:ℤ) : ℝ) = ((18757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2141 : ((((452242487783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18757 < q → q < 18773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18773).mp (by decide +kernel))) hgap
  have hprev := s2L_2140
  have hrat : ((452242487783 : ℚ) / 1000000000000) ≤ ((226121242473 : ℚ) / 500000000000) + (18773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242487783 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121242473 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18773:ℚ)^(-2:ℤ) : ℝ) = ((18773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2142 : ((((56530311327 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18773 < q → q < 18787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18787).mp (by decide +kernel))) hgap
  have hprev := s2L_2141
  have hrat : ((56530311327 : ℚ) / 125000000000) ≤ ((452242487783 : ℚ) / 1000000000000) + (18787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530311327 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242487783 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18787:ℚ)^(-2:ℤ) : ℝ) = ((18787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2143 : ((((452242493447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18787 < q → q < 18793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18793).mp (by decide +kernel))) hgap
  have hprev := s2L_2142
  have hrat : ((452242493447 : ℚ) / 1000000000000) ≤ ((56530311327 : ℚ) / 125000000000) + (18793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242493447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530311327 : ℚ) / 125000000000) : ℚ) : ℝ) + ((18793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18793:ℚ)^(-2:ℤ) : ℝ) = ((18793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2144 : ((((452242496277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18797, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18793 < q → q < 18797 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18797).mp (by decide +kernel))) hgap
  have hprev := s2L_2143
  have hrat : ((452242496277 : ℚ) / 1000000000000) ≤ ((452242493447 : ℚ) / 1000000000000) + (18797:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242496277 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242493447 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18797:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18797:ℚ)^(-2:ℤ) : ℝ) = ((18797:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2145 : ((((90448499821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18797 < q → q < 18803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18803).mp (by decide +kernel))) hgap
  have hprev := s2L_2144
  have hrat : ((90448499821 : ℚ) / 200000000000) ≤ ((452242496277 : ℚ) / 1000000000000) + (18803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448499821 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242496277 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18803:ℚ)^(-2:ℤ) : ℝ) = ((18803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2146 : ((((226121250961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18803 < q → q < 18839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18839).mp (by decide +kernel))) hgap
  have hprev := s2L_2145
  have hrat : ((226121250961 : ℚ) / 500000000000) ≤ ((90448499821 : ℚ) / 200000000000) + (18839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121250961 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448499821 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18839:ℚ)^(-2:ℤ) : ℝ) = ((18839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2147 : ((((452242504733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18839 < q → q < 18859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18859).mp (by decide +kernel))) hgap
  have hprev := s2L_2146
  have hrat : ((452242504733 : ℚ) / 1000000000000) ≤ ((226121250961 : ℚ) / 500000000000) + (18859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242504733 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121250961 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18859:ℚ)^(-2:ℤ) : ℝ) = ((18859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2148 : ((((452242507541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18869, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18859 < q → q < 18869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18869).mp (by decide +kernel))) hgap
  have hprev := s2L_2147
  have hrat : ((452242507541 : ℚ) / 1000000000000) ≤ ((452242504733 : ℚ) / 1000000000000) + (18869:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242507541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242504733 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18869:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18869:ℚ)^(-2:ℤ) : ℝ) = ((18869:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2149 : ((((22612125517 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18899, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18869 < q → q < 18899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18899).mp (by decide +kernel))) hgap
  have hprev := s2L_2148
  have hrat : ((22612125517 : ℚ) / 50000000000) ≤ ((452242507541 : ℚ) / 1000000000000) + (18899:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612125517 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242507541 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18899:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18899:ℚ)^(-2:ℤ) : ℝ) = ((18899:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2150 : ((((28265157071 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18899 < q → q < 18911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18911).mp (by decide +kernel))) hgap
  have hprev := s2L_2149
  have hrat : ((28265157071 : ℚ) / 62500000000) ≤ ((22612125517 : ℚ) / 50000000000) + (18911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265157071 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((22612125517 : ℚ) / 50000000000) : ℚ) : ℝ) + ((18911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18911:ℚ)^(-2:ℤ) : ℝ) = ((18911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2151 : ((((452242515931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18911 < q → q < 18913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18913).mp (by decide +kernel))) hgap
  have hprev := s2L_2150
  have hrat : ((452242515931 : ℚ) / 1000000000000) ≤ ((28265157071 : ℚ) / 62500000000) + (18913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242515931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265157071 : ℚ) / 62500000000) : ℚ) : ℝ) + ((18913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18913:ℚ)^(-2:ℤ) : ℝ) = ((18913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2152 : ((((18089700749 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18913 < q → q < 18917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18917).mp (by decide +kernel))) hgap
  have hprev := s2L_2151
  have hrat : ((18089700749 : ℚ) / 40000000000) ≤ ((452242515931 : ℚ) / 1000000000000) + (18917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089700749 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452242515931 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18917:ℚ)^(-2:ℤ) : ℝ) = ((18917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2153 : ((((226121260759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18917 < q → q < 18919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18919).mp (by decide +kernel))) hgap
  have hprev := s2L_2152
  have hrat : ((226121260759 : ℚ) / 500000000000) ≤ ((18089700749 : ℚ) / 40000000000) + (18919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121260759 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089700749 : ℚ) / 40000000000) : ℚ) : ℝ) + ((18919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18919:ℚ)^(-2:ℤ) : ℝ) = ((18919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2154 : ((((452242524303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18919 < q → q < 18947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18947).mp (by decide +kernel))) hgap
  have hprev := s2L_2153
  have hrat : ((452242524303 : ℚ) / 1000000000000) ≤ ((226121260759 : ℚ) / 500000000000) + (18947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242524303 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121260759 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18947:ℚ)^(-2:ℤ) : ℝ) = ((18947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2155 : ((((90448505417 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18947 < q → q < 18959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18959).mp (by decide +kernel))) hgap
  have hprev := s2L_2154
  have hrat : ((90448505417 : ℚ) / 200000000000) ≤ ((452242524303 : ℚ) / 1000000000000) + (18959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448505417 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242524303 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((18959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18959:ℚ)^(-2:ℤ) : ℝ) = ((18959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2156 : ((((226121264931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18959 < q → q < 18973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18973).mp (by decide +kernel))) hgap
  have hprev := s2L_2155
  have hrat : ((226121264931 : ℚ) / 500000000000) ≤ ((90448505417 : ℚ) / 200000000000) + (18973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121264931 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448505417 : ℚ) / 200000000000) : ℚ) : ℝ) + ((18973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18973:ℚ)^(-2:ℤ) : ℝ) = ((18973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2157 : ((((226121266319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 18979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18973 < q → q < 18979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 18979).mp (by decide +kernel))) hgap
  have hprev := s2L_2156
  have hrat : ((226121266319 : ℚ) / 500000000000) ≤ ((226121264931 : ℚ) / 500000000000) + (18979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121266319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121264931 : ℚ) / 500000000000) : ℚ) : ℝ) + ((18979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((18979:ℚ)^(-2:ℤ) : ℝ) = ((18979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2158 : ((((452242535407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 18979 < q → q < 19001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19001).mp (by decide +kernel))) hgap
  have hprev := s2L_2157
  have hrat : ((452242535407 : ℚ) / 1000000000000) ≤ ((226121266319 : ℚ) / 500000000000) + (19001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242535407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121266319 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19001:ℚ)^(-2:ℤ) : ℝ) = ((19001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2159 : ((((226121269087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19001 < q → q < 19009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19009).mp (by decide +kernel))) hgap
  have hprev := s2L_2158
  have hrat : ((226121269087 : ℚ) / 500000000000) ≤ ((452242535407 : ℚ) / 1000000000000) + (19009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121269087 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242535407 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19009:ℚ)^(-2:ℤ) : ℝ) = ((19009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2160 : ((((22612127047 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19009 < q → q < 19013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19013).mp (by decide +kernel))) hgap
  have hprev := s2L_2159
  have hrat : ((22612127047 : ℚ) / 50000000000) ≤ ((226121269087 : ℚ) / 500000000000) + (19013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612127047 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121269087 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19013:ℚ)^(-2:ℤ) : ℝ) = ((19013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2161 : ((((452242543701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19013 < q → q < 19031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19031).mp (by decide +kernel))) hgap
  have hprev := s2L_2160
  have hrat : ((452242543701 : ℚ) / 1000000000000) ≤ ((22612127047 : ℚ) / 50000000000) + (19031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242543701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612127047 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19031:ℚ)^(-2:ℤ) : ℝ) = ((19031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2162 : ((((22612127323 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19031 < q → q < 19037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19037).mp (by decide +kernel))) hgap
  have hprev := s2L_2161
  have hrat : ((22612127323 : ℚ) / 50000000000) ≤ ((452242543701 : ℚ) / 1000000000000) + (19037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612127323 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242543701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19037:ℚ)^(-2:ℤ) : ℝ) = ((19037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2163 : ((((90448509843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19037 < q → q < 19051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19051).mp (by decide +kernel))) hgap
  have hprev := s2L_2162
  have hrat : ((90448509843 : ℚ) / 200000000000) ≤ ((22612127323 : ℚ) / 50000000000) + (19051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448509843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612127323 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19051:ℚ)^(-2:ℤ) : ℝ) = ((19051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2164 : ((((90448510393 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19051 < q → q < 19069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19069).mp (by decide +kernel))) hgap
  have hprev := s2L_2163
  have hrat : ((90448510393 : ℚ) / 200000000000) ≤ ((90448509843 : ℚ) / 200000000000) + (19069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448510393 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448509843 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19069:ℚ)^(-2:ℤ) : ℝ) = ((19069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2165 : ((((452242554713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19069 < q → q < 19073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19073).mp (by decide +kernel))) hgap
  have hprev := s2L_2164
  have hrat : ((452242554713 : ℚ) / 1000000000000) ≤ ((90448510393 : ℚ) / 200000000000) + (19073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242554713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448510393 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19073:ℚ)^(-2:ℤ) : ℝ) = ((19073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2166 : ((((22612127873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19073 < q → q < 19079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19079).mp (by decide +kernel))) hgap
  have hprev := s2L_2165
  have hrat : ((22612127873 : ℚ) / 50000000000) ≤ ((452242554713 : ℚ) / 1000000000000) + (19079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612127873 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242554713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19079:ℚ)^(-2:ℤ) : ℝ) = ((19079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2167 : ((((226121280103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19079 < q → q < 19081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19081).mp (by decide +kernel))) hgap
  have hprev := s2L_2166
  have hrat : ((226121280103 : ℚ) / 500000000000) ≤ ((22612127873 : ℚ) / 50000000000) + (19081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121280103 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612127873 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19081:ℚ)^(-2:ℤ) : ℝ) = ((19081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2168 : ((((9044851259 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19081 < q → q < 19087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19087).mp (by decide +kernel))) hgap
  have hprev := s2L_2167
  have hrat : ((9044851259 : ℚ) / 20000000000) ≤ ((226121280103 : ℚ) / 500000000000) + (19087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044851259 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226121280103 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19087:ℚ)^(-2:ℤ) : ℝ) = ((19087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2169 : ((((90448513137 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19087 < q → q < 19121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19121).mp (by decide +kernel))) hgap
  have hprev := s2L_2168
  have hrat : ((90448513137 : ℚ) / 200000000000) ≤ ((9044851259 : ℚ) / 20000000000) + (19121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448513137 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9044851259 : ℚ) / 20000000000) : ℚ) : ℝ) + ((19121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19121:ℚ)^(-2:ℤ) : ℝ) = ((19121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2170 : ((((226121284207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19121 < q → q < 19139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19139).mp (by decide +kernel))) hgap
  have hprev := s2L_2169
  have hrat : ((226121284207 : ℚ) / 500000000000) ≤ ((90448513137 : ℚ) / 200000000000) + (19139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121284207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448513137 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19139:ℚ)^(-2:ℤ) : ℝ) = ((19139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2171 : ((((452242571143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19141, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19139 < q → q < 19141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19141).mp (by decide +kernel))) hgap
  have hprev := s2L_2170
  have hrat : ((452242571143 : ℚ) / 1000000000000) ≤ ((226121284207 : ℚ) / 500000000000) + (19141:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242571143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121284207 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19141:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19141:ℚ)^(-2:ℤ) : ℝ) = ((19141:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2172 : ((((452242573867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19141 < q → q < 19157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19157).mp (by decide +kernel))) hgap
  have hprev := s2L_2171
  have hrat : ((452242573867 : ℚ) / 1000000000000) ≤ ((452242571143 : ℚ) / 1000000000000) + (19157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242573867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242571143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19157:ℚ)^(-2:ℤ) : ℝ) = ((19157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2173 : ((((45224257659 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19157 < q → q < 19163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19163).mp (by decide +kernel))) hgap
  have hprev := s2L_2172
  have hrat : ((45224257659 : ℚ) / 100000000000) ≤ ((452242573867 : ℚ) / 1000000000000) + (19163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224257659 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242573867 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19163:ℚ)^(-2:ℤ) : ℝ) = ((19163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2174 : ((((113060644827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19163 < q → q < 19181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19181).mp (by decide +kernel))) hgap
  have hprev := s2L_2173
  have hrat : ((113060644827 : ℚ) / 250000000000) ≤ ((45224257659 : ℚ) / 100000000000) + (19181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060644827 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45224257659 : ℚ) / 100000000000) : ℚ) : ℝ) + ((19181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19181:ℚ)^(-2:ℤ) : ℝ) = ((19181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2175 : ((((18089703281 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19181 < q → q < 19183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19183).mp (by decide +kernel))) hgap
  have hprev := s2L_2174
  have hrat : ((18089703281 : ℚ) / 40000000000) ≤ ((113060644827 : ℚ) / 250000000000) + (19183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089703281 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113060644827 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19183:ℚ)^(-2:ℤ) : ℝ) = ((19183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2176 : ((((90448516947 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19183 < q → q < 19207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19207).mp (by decide +kernel))) hgap
  have hprev := s2L_2175
  have hrat : ((90448516947 : ℚ) / 200000000000) ≤ ((18089703281 : ℚ) / 40000000000) + (19207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448516947 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089703281 : ℚ) / 40000000000) : ℚ) : ℝ) + ((19207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19207:ℚ)^(-2:ℤ) : ℝ) = ((19207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2177 : ((((113060646861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19207 < q → q < 19211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19211).mp (by decide +kernel))) hgap
  have hprev := s2L_2176
  have hrat : ((113060646861 : ℚ) / 250000000000) ≤ ((90448516947 : ℚ) / 200000000000) + (19211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060646861 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448516947 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19211:ℚ)^(-2:ℤ) : ℝ) = ((19211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2178 : ((((452242590153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19213, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19211 < q → q < 19213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19213).mp (by decide +kernel))) hgap
  have hprev := s2L_2177
  have hrat : ((452242590153 : ℚ) / 1000000000000) ≤ ((113060646861 : ℚ) / 250000000000) + (19213:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242590153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060646861 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19213:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19213:ℚ)^(-2:ℤ) : ℝ) = ((19213:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2179 : ((((22612129643 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19213 < q → q < 19219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19219).mp (by decide +kernel))) hgap
  have hprev := s2L_2178
  have hrat : ((22612129643 : ℚ) / 50000000000) ≤ ((452242590153 : ℚ) / 1000000000000) + (19219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612129643 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242590153 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19219:ℚ)^(-2:ℤ) : ℝ) = ((19219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2180 : ((((452242595563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19219 < q → q < 19231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19231).mp (by decide +kernel))) hgap
  have hprev := s2L_2179
  have hrat : ((452242595563 : ℚ) / 1000000000000) ≤ ((22612129643 : ℚ) / 50000000000) + (19231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242595563 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612129643 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19231:ℚ)^(-2:ℤ) : ℝ) = ((19231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2181 : ((((90448519653 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19231 < q → q < 19237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19237).mp (by decide +kernel))) hgap
  have hprev := s2L_2180
  have hrat : ((90448519653 : ℚ) / 200000000000) ≤ ((452242595563 : ℚ) / 1000000000000) + (19237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448519653 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242595563 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19237:ℚ)^(-2:ℤ) : ℝ) = ((19237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2182 : ((((452242600963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19237 < q → q < 19249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19249).mp (by decide +kernel))) hgap
  have hprev := s2L_2181
  have hrat : ((452242600963 : ℚ) / 1000000000000) ≤ ((90448519653 : ℚ) / 200000000000) + (19249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242600963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448519653 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19249:ℚ)^(-2:ℤ) : ℝ) = ((19249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2183 : ((((452242603659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19249 < q → q < 19259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19259).mp (by decide +kernel))) hgap
  have hprev := s2L_2182
  have hrat : ((452242603659 : ℚ) / 1000000000000) ≤ ((452242600963 : ℚ) / 1000000000000) + (19259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242603659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242600963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19259:ℚ)^(-2:ℤ) : ℝ) = ((19259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2184 : ((((28265162897 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19259 < q → q < 19267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19267).mp (by decide +kernel))) hgap
  have hprev := s2L_2183
  have hrat : ((28265162897 : ℚ) / 62500000000) ≤ ((452242603659 : ℚ) / 1000000000000) + (19267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265162897 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242603659 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19267:ℚ)^(-2:ℤ) : ℝ) = ((19267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2185 : ((((113060652261 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19267 < q → q < 19273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19273).mp (by decide +kernel))) hgap
  have hprev := s2L_2184
  have hrat : ((113060652261 : ℚ) / 250000000000) ≤ ((28265162897 : ℚ) / 62500000000) + (19273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060652261 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28265162897 : ℚ) / 62500000000) : ℚ) : ℝ) + ((19273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19273:ℚ)^(-2:ℤ) : ℝ) = ((19273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2186 : ((((452242611731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19273 < q → q < 19289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19289).mp (by decide +kernel))) hgap
  have hprev := s2L_2185
  have hrat : ((452242611731 : ℚ) / 1000000000000) ≤ ((113060652261 : ℚ) / 250000000000) + (19289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242611731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060652261 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19289:ℚ)^(-2:ℤ) : ℝ) = ((19289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2187 : ((((90448522883 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19289 < q → q < 19301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19301).mp (by decide +kernel))) hgap
  have hprev := s2L_2186
  have hrat : ((90448522883 : ℚ) / 200000000000) ≤ ((452242611731 : ℚ) / 1000000000000) + (19301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448522883 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242611731 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19301:ℚ)^(-2:ℤ) : ℝ) = ((19301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2188 : ((((452242617097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19301 < q → q < 19309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19309).mp (by decide +kernel))) hgap
  have hprev := s2L_2187
  have hrat : ((452242617097 : ℚ) / 1000000000000) ≤ ((90448522883 : ℚ) / 200000000000) + (19309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242617097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448522883 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19309:ℚ)^(-2:ℤ) : ℝ) = ((19309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2189 : ((((3533145467 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19309 < q → q < 19319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19319).mp (by decide +kernel))) hgap
  have hprev := s2L_2188
  have hrat : ((3533145467 : ℚ) / 7812500000) ≤ ((452242617097 : ℚ) / 1000000000000) + (19319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533145467 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((452242617097 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19319:ℚ)^(-2:ℤ) : ℝ) = ((19319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2190 : ((((452242622451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19319 < q → q < 19333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19333).mp (by decide +kernel))) hgap
  have hprev := s2L_2189
  have hrat : ((452242622451 : ℚ) / 1000000000000) ≤ ((3533145467 : ℚ) / 7812500000) + (19333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242622451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3533145467 : ℚ) / 7812500000) : ℚ) : ℝ) + ((19333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19333:ℚ)^(-2:ℤ) : ℝ) = ((19333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2191 : ((((90448525023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19333 < q → q < 19373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19373).mp (by decide +kernel))) hgap
  have hprev := s2L_2190
  have hrat : ((90448525023 : ℚ) / 200000000000) ≤ ((452242622451 : ℚ) / 1000000000000) + (19373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448525023 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242622451 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19373:ℚ)^(-2:ℤ) : ℝ) = ((19373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2192 : ((((452242627777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19373 < q → q < 19379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19379).mp (by decide +kernel))) hgap
  have hprev := s2L_2191
  have hrat : ((452242627777 : ℚ) / 1000000000000) ≤ ((90448525023 : ℚ) / 200000000000) + (19379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242627777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448525023 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19379:ℚ)^(-2:ℤ) : ℝ) = ((19379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2193 : ((((452242630439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19379 < q → q < 19381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19381).mp (by decide +kernel))) hgap
  have hprev := s2L_2192
  have hrat : ((452242630439 : ℚ) / 1000000000000) ≤ ((452242627777 : ℚ) / 1000000000000) + (19381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242630439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242627777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19381:ℚ)^(-2:ℤ) : ℝ) = ((19381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2194 : ((((452242633099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19381 < q → q < 19387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19387).mp (by decide +kernel))) hgap
  have hprev := s2L_2193
  have hrat : ((452242633099 : ℚ) / 1000000000000) ≤ ((452242630439 : ℚ) / 1000000000000) + (19387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242633099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242630439 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19387:ℚ)^(-2:ℤ) : ℝ) = ((19387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2195 : ((((226121317879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19387 < q → q < 19391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19391).mp (by decide +kernel))) hgap
  have hprev := s2L_2194
  have hrat : ((226121317879 : ℚ) / 500000000000) ≤ ((452242633099 : ℚ) / 1000000000000) + (19391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121317879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242633099 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19391:ℚ)^(-2:ℤ) : ℝ) = ((19391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2196 : ((((226121319207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19403, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19391 < q → q < 19403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19403).mp (by decide +kernel))) hgap
  have hprev := s2L_2195
  have hrat : ((226121319207 : ℚ) / 500000000000) ≤ ((226121317879 : ℚ) / 500000000000) + (19403:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121319207 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121317879 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19403:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19403:ℚ)^(-2:ℤ) : ℝ) = ((19403:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2197 : ((((226121320533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19403 < q → q < 19417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19417).mp (by decide +kernel))) hgap
  have hprev := s2L_2196
  have hrat : ((226121320533 : ℚ) / 500000000000) ≤ ((226121319207 : ℚ) / 500000000000) + (19417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121320533 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121319207 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19417:ℚ)^(-2:ℤ) : ℝ) = ((19417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2198 : ((((452242643717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19417 < q → q < 19421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19421).mp (by decide +kernel))) hgap
  have hprev := s2L_2197
  have hrat : ((452242643717 : ℚ) / 1000000000000) ≤ ((226121320533 : ℚ) / 500000000000) + (19421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242643717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121320533 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19421:ℚ)^(-2:ℤ) : ℝ) = ((19421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2199 : ((((452242646367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19421 < q → q < 19423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19423).mp (by decide +kernel))) hgap
  have hprev := s2L_2198
  have hrat : ((452242646367 : ℚ) / 1000000000000) ≤ ((452242643717 : ℚ) / 1000000000000) + (19423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242646367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242643717 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19423:ℚ)^(-2:ℤ) : ℝ) = ((19423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2200 : ((((56530331127 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19423 < q → q < 19427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19427).mp (by decide +kernel))) hgap
  have hprev := s2L_2199
  have hrat : ((56530331127 : ℚ) / 125000000000) ≤ ((452242646367 : ℚ) / 1000000000000) + (19427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530331127 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242646367 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19427:ℚ)^(-2:ℤ) : ℝ) = ((19427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2201 : ((((90448530333 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19427 < q → q < 19429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19429).mp (by decide +kernel))) hgap
  have hprev := s2L_2200
  have hrat : ((90448530333 : ℚ) / 200000000000) ≤ ((56530331127 : ℚ) / 125000000000) + (19429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448530333 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530331127 : ℚ) / 125000000000) : ℚ) : ℝ) + ((19429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19429:ℚ)^(-2:ℤ) : ℝ) = ((19429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2202 : ((((452242654313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19429 < q → q < 19433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19433).mp (by decide +kernel))) hgap
  have hprev := s2L_2201
  have hrat : ((452242654313 : ℚ) / 1000000000000) ≤ ((90448530333 : ℚ) / 200000000000) + (19433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242654313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448530333 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19433:ℚ)^(-2:ℤ) : ℝ) = ((19433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2203 : ((((226121328479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19433 < q → q < 19441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19441).mp (by decide +kernel))) hgap
  have hprev := s2L_2202
  have hrat : ((226121328479 : ℚ) / 500000000000) ≤ ((452242654313 : ℚ) / 1000000000000) + (19441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121328479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242654313 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19441:ℚ)^(-2:ℤ) : ℝ) = ((19441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2204 : ((((226121329801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19441 < q → q < 19447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19447).mp (by decide +kernel))) hgap
  have hprev := s2L_2203
  have hrat : ((226121329801 : ℚ) / 500000000000) ≤ ((226121328479 : ℚ) / 500000000000) + (19447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121329801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121328479 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19447:ℚ)^(-2:ℤ) : ℝ) = ((19447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2205 : ((((452242662243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19447 < q → q < 19457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19457).mp (by decide +kernel))) hgap
  have hprev := s2L_2204
  have hrat : ((452242662243 : ℚ) / 1000000000000) ≤ ((226121329801 : ℚ) / 500000000000) + (19457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242662243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121329801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19457:ℚ)^(-2:ℤ) : ℝ) = ((19457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2206 : ((((226121332441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19457 < q → q < 19463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19463).mp (by decide +kernel))) hgap
  have hprev := s2L_2205
  have hrat : ((226121332441 : ℚ) / 500000000000) ≤ ((452242662243 : ℚ) / 1000000000000) + (19463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121332441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242662243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19463:ℚ)^(-2:ℤ) : ℝ) = ((19463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2207 : ((((44164323 : ℚ) / 97656250) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19463 < q → q < 19469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19469).mp (by decide +kernel))) hgap
  have hprev := s2L_2206
  have hrat : ((44164323 : ℚ) / 97656250) ≤ ((226121332441 : ℚ) / 500000000000) + (19469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((44164323 : ℚ) / 97656250) : ℚ) : ℝ) ≤ ((((226121332441 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19469:ℚ)^(-2:ℤ) : ℝ) = ((19469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2208 : ((((452242670157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19469 < q → q < 19471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19471).mp (by decide +kernel))) hgap
  have hprev := s2L_2207
  have hrat : ((452242670157 : ℚ) / 1000000000000) ≤ ((44164323 : ℚ) / 97656250) + (19471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242670157 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((44164323 : ℚ) / 97656250) : ℚ) : ℝ) + ((19471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19471:ℚ)^(-2:ℤ) : ℝ) = ((19471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2209 : ((((452242672793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19471 < q → q < 19477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19477).mp (by decide +kernel))) hgap
  have hprev := s2L_2208
  have hrat : ((452242672793 : ℚ) / 1000000000000) ≤ ((452242670157 : ℚ) / 1000000000000) + (19477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242672793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242670157 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19477:ℚ)^(-2:ℤ) : ℝ) = ((19477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2210 : ((((452242675427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19477 < q → q < 19483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19483).mp (by decide +kernel))) hgap
  have hprev := s2L_2209
  have hrat : ((452242675427 : ℚ) / 1000000000000) ≤ ((452242672793 : ℚ) / 1000000000000) + (19483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242675427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242672793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19483:ℚ)^(-2:ℤ) : ℝ) = ((19483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2211 : ((((452242678059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19483 < q → q < 19489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19489).mp (by decide +kernel))) hgap
  have hprev := s2L_2210
  have hrat : ((452242678059 : ℚ) / 1000000000000) ≤ ((452242675427 : ℚ) / 1000000000000) + (19489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242678059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242675427 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19489:ℚ)^(-2:ℤ) : ℝ) = ((19489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2212 : ((((28265167543 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19489 < q → q < 19501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19501).mp (by decide +kernel))) hgap
  have hprev := s2L_2211
  have hrat : ((28265167543 : ℚ) / 62500000000) ≤ ((452242678059 : ℚ) / 1000000000000) + (19501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265167543 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242678059 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19501:ℚ)^(-2:ℤ) : ℝ) = ((19501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2213 : ((((90448536663 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19507, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19501 < q → q < 19507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19507).mp (by decide +kernel))) hgap
  have hprev := s2L_2212
  have hrat : ((90448536663 : ℚ) / 200000000000) ≤ ((28265167543 : ℚ) / 62500000000) + (19507:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448536663 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28265167543 : ℚ) / 62500000000) : ℚ) : ℝ) + ((19507:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19507:ℚ)^(-2:ℤ) : ℝ) = ((19507:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2214 : ((((28265167871 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19507 < q → q < 19531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19531).mp (by decide +kernel))) hgap
  have hprev := s2L_2213
  have hrat : ((28265167871 : ℚ) / 62500000000) ≤ ((90448536663 : ℚ) / 200000000000) + (19531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265167871 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90448536663 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19531:ℚ)^(-2:ℤ) : ℝ) = ((19531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2215 : ((((226121344277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19531 < q → q < 19541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19541).mp (by decide +kernel))) hgap
  have hprev := s2L_2214
  have hrat : ((226121344277 : ℚ) / 500000000000) ≤ ((28265167871 : ℚ) / 62500000000) + (19541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121344277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265167871 : ℚ) / 62500000000) : ℚ) : ℝ) + ((19541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19541:ℚ)^(-2:ℤ) : ℝ) = ((19541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2216 : ((((113060672793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19541 < q → q < 19543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19543).mp (by decide +kernel))) hgap
  have hprev := s2L_2215
  have hrat : ((113060672793 : ℚ) / 250000000000) ≤ ((226121344277 : ℚ) / 500000000000) + (19543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060672793 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121344277 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19543:ℚ)^(-2:ℤ) : ℝ) = ((19543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2217 : ((((452242693787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19543 < q → q < 19553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19553).mp (by decide +kernel))) hgap
  have hprev := s2L_2216
  have hrat : ((452242693787 : ℚ) / 1000000000000) ≤ ((113060672793 : ℚ) / 250000000000) + (19553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242693787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060672793 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19553:ℚ)^(-2:ℤ) : ℝ) = ((19553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2218 : ((((452242696401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19553 < q → q < 19559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19559).mp (by decide +kernel))) hgap
  have hprev := s2L_2217
  have hrat : ((452242696401 : ℚ) / 1000000000000) ≤ ((452242693787 : ℚ) / 1000000000000) + (19559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242696401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242693787 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19559:ℚ)^(-2:ℤ) : ℝ) = ((19559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2219 : ((((452242699011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19559 < q → q < 19571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19571).mp (by decide +kernel))) hgap
  have hprev := s2L_2218
  have hrat : ((452242699011 : ℚ) / 1000000000000) ≤ ((452242696401 : ℚ) / 1000000000000) + (19571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242699011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242696401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19571:ℚ)^(-2:ℤ) : ℝ) = ((19571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2220 : ((((22612135081 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19571 < q → q < 19577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19577).mp (by decide +kernel))) hgap
  have hprev := s2L_2219
  have hrat : ((22612135081 : ℚ) / 50000000000) ≤ ((452242699011 : ℚ) / 1000000000000) + (19577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612135081 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242699011 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19577:ℚ)^(-2:ℤ) : ℝ) = ((19577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2221 : ((((452242704227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19577 < q → q < 19583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19583).mp (by decide +kernel))) hgap
  have hprev := s2L_2220
  have hrat : ((452242704227 : ℚ) / 1000000000000) ≤ ((22612135081 : ℚ) / 50000000000) + (19583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242704227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612135081 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19583:ℚ)^(-2:ℤ) : ℝ) = ((19583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2222 : ((((45224270683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19583 < q → q < 19597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19597).mp (by decide +kernel))) hgap
  have hprev := s2L_2221
  have hrat : ((45224270683 : ℚ) / 100000000000) ≤ ((452242704227 : ℚ) / 1000000000000) + (19597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224270683 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242704227 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19597:ℚ)^(-2:ℤ) : ℝ) = ((19597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2223 : ((((56530338679 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19597 < q → q < 19603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19603).mp (by decide +kernel))) hgap
  have hprev := s2L_2222
  have hrat : ((56530338679 : ℚ) / 125000000000) ≤ ((45224270683 : ℚ) / 100000000000) + (19603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530338679 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45224270683 : ℚ) / 100000000000) : ℚ) : ℝ) + ((19603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19603:ℚ)^(-2:ℤ) : ℝ) = ((19603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2224 : ((((14132584751 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19603 < q → q < 19609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19609).mp (by decide +kernel))) hgap
  have hprev := s2L_2223
  have hrat : ((14132584751 : ℚ) / 31250000000) ≤ ((56530338679 : ℚ) / 125000000000) + (19609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132584751 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((56530338679 : ℚ) / 125000000000) : ℚ) : ℝ) + ((19609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19609:ℚ)^(-2:ℤ) : ℝ) = ((19609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2225 : ((((226121357309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19609 < q → q < 19661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19661).mp (by decide +kernel))) hgap
  have hprev := s2L_2224
  have hrat : ((226121357309 : ℚ) / 500000000000) ≤ ((14132584751 : ℚ) / 31250000000) + (19661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121357309 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14132584751 : ℚ) / 31250000000) : ℚ) : ℝ) + ((19661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19661:ℚ)^(-2:ℤ) : ℝ) = ((19661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2226 : ((((452242717199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19661 < q → q < 19681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19681).mp (by decide +kernel))) hgap
  have hprev := s2L_2225
  have hrat : ((452242717199 : ℚ) / 1000000000000) ≤ ((226121357309 : ℚ) / 500000000000) + (19681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242717199 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121357309 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19681:ℚ)^(-2:ℤ) : ℝ) = ((19681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2227 : ((((452242719779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19681 < q → q < 19687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19687).mp (by decide +kernel))) hgap
  have hprev := s2L_2226
  have hrat : ((452242719779 : ℚ) / 1000000000000) ≤ ((452242717199 : ℚ) / 1000000000000) + (19687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242719779 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242717199 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19687:ℚ)^(-2:ℤ) : ℝ) = ((19687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2228 : ((((113060680589 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19687 < q → q < 19697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19697).mp (by decide +kernel))) hgap
  have hprev := s2L_2227
  have hrat : ((113060680589 : ℚ) / 250000000000) ≤ ((452242719779 : ℚ) / 1000000000000) + (19697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060680589 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242719779 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19697:ℚ)^(-2:ℤ) : ℝ) = ((19697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2229 : ((((113060681233 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19697 < q → q < 19699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19699).mp (by decide +kernel))) hgap
  have hprev := s2L_2228
  have hrat : ((113060681233 : ℚ) / 250000000000) ≤ ((113060680589 : ℚ) / 250000000000) + (19699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060681233 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060680589 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19699:ℚ)^(-2:ℤ) : ℝ) = ((19699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2230 : ((((226121363753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19699 < q → q < 19709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19709).mp (by decide +kernel))) hgap
  have hprev := s2L_2229
  have hrat : ((226121363753 : ℚ) / 500000000000) ≤ ((113060681233 : ℚ) / 250000000000) + (19709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121363753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060681233 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19709:ℚ)^(-2:ℤ) : ℝ) = ((19709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2231 : ((((226121365039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19709 < q → q < 19717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19717).mp (by decide +kernel))) hgap
  have hprev := s2L_2230
  have hrat : ((226121365039 : ℚ) / 500000000000) ≤ ((226121363753 : ℚ) / 500000000000) + (19717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121365039 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121363753 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19717:ℚ)^(-2:ℤ) : ℝ) = ((19717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2232 : ((((452242732647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19717 < q → q < 19727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19727).mp (by decide +kernel))) hgap
  have hprev := s2L_2231
  have hrat : ((452242732647 : ℚ) / 1000000000000) ≤ ((226121365039 : ℚ) / 500000000000) + (19727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242732647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121365039 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19727:ℚ)^(-2:ℤ) : ℝ) = ((19727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2233 : ((((452242735213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19727 < q → q < 19739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19739).mp (by decide +kernel))) hgap
  have hprev := s2L_2232
  have hrat : ((452242735213 : ℚ) / 1000000000000) ≤ ((452242732647 : ℚ) / 1000000000000) + (19739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242735213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242732647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19739:ℚ)^(-2:ℤ) : ℝ) = ((19739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2234 : ((((28265171111 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19739 < q → q < 19751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19751).mp (by decide +kernel))) hgap
  have hprev := s2L_2233
  have hrat : ((28265171111 : ℚ) / 62500000000) ≤ ((452242735213 : ℚ) / 1000000000000) + (19751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265171111 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242735213 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19751:ℚ)^(-2:ℤ) : ℝ) = ((19751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2235 : ((((226121370169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19751 < q → q < 19753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19753).mp (by decide +kernel))) hgap
  have hprev := s2L_2234
  have hrat : ((226121370169 : ℚ) / 500000000000) ≤ ((28265171111 : ℚ) / 62500000000) + (19753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121370169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28265171111 : ℚ) / 62500000000) : ℚ) : ℝ) + ((19753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19753:ℚ)^(-2:ℤ) : ℝ) = ((19753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2236 : ((((452242742899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19753 < q → q < 19759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19759).mp (by decide +kernel))) hgap
  have hprev := s2L_2235
  have hrat : ((452242742899 : ℚ) / 1000000000000) ≤ ((226121370169 : ℚ) / 500000000000) + (19759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242742899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121370169 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19759:ℚ)^(-2:ℤ) : ℝ) = ((19759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2237 : ((((452242745459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19759 < q → q < 19763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19763).mp (by decide +kernel))) hgap
  have hprev := s2L_2236
  have hrat : ((452242745459 : ℚ) / 1000000000000) ≤ ((452242742899 : ℚ) / 1000000000000) + (19763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242745459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242742899 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19763:ℚ)^(-2:ℤ) : ℝ) = ((19763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2238 : ((((90448549603 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19763 < q → q < 19777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19777).mp (by decide +kernel))) hgap
  have hprev := s2L_2237
  have hrat : ((90448549603 : ℚ) / 200000000000) ≤ ((452242745459 : ℚ) / 1000000000000) + (19777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448549603 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452242745459 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19777:ℚ)^(-2:ℤ) : ℝ) = ((19777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2239 : ((((452242750567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19777 < q → q < 19793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19793).mp (by decide +kernel))) hgap
  have hprev := s2L_2238
  have hrat : ((452242750567 : ℚ) / 1000000000000) ≤ ((90448549603 : ℚ) / 200000000000) + (19793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242750567 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448549603 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19793:ℚ)^(-2:ℤ) : ℝ) = ((19793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2240 : ((((452242753117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19793 < q → q < 19801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19801).mp (by decide +kernel))) hgap
  have hprev := s2L_2239
  have hrat : ((452242753117 : ℚ) / 1000000000000) ≤ ((452242750567 : ℚ) / 1000000000000) + (19801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242753117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242750567 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19801:ℚ)^(-2:ℤ) : ℝ) = ((19801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2241 : ((((28265172229 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19801 < q → q < 19813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19813).mp (by decide +kernel))) hgap
  have hprev := s2L_2240
  have hrat : ((28265172229 : ℚ) / 62500000000) ≤ ((452242753117 : ℚ) / 1000000000000) + (19813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265172229 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242753117 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19813:ℚ)^(-2:ℤ) : ℝ) = ((19813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2242 : ((((452242758209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19813 < q → q < 19819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19819).mp (by decide +kernel))) hgap
  have hprev := s2L_2241
  have hrat : ((452242758209 : ℚ) / 1000000000000) ≤ ((28265172229 : ℚ) / 62500000000) + (19819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242758209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265172229 : ℚ) / 62500000000) : ℚ) : ℝ) + ((19819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19819:ℚ)^(-2:ℤ) : ℝ) = ((19819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2243 : ((((452242760749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19819 < q → q < 19841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19841).mp (by decide +kernel))) hgap
  have hprev := s2L_2242
  have hrat : ((452242760749 : ℚ) / 1000000000000) ≤ ((452242758209 : ℚ) / 1000000000000) + (19841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242760749 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242758209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19841:ℚ)^(-2:ℤ) : ℝ) = ((19841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2244 : ((((56530345411 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19841 < q → q < 19843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19843).mp (by decide +kernel))) hgap
  have hprev := s2L_2243
  have hrat : ((56530345411 : ℚ) / 125000000000) ≤ ((452242760749 : ℚ) / 1000000000000) + (19843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530345411 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242760749 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19843:ℚ)^(-2:ℤ) : ℝ) = ((19843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2245 : ((((18089710633 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19843 < q → q < 19853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19853).mp (by decide +kernel))) hgap
  have hprev := s2L_2244
  have hrat : ((18089710633 : ℚ) / 40000000000) ≤ ((56530345411 : ℚ) / 125000000000) + (19853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089710633 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((56530345411 : ℚ) / 125000000000) : ℚ) : ℝ) + ((19853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19853:ℚ)^(-2:ℤ) : ℝ) = ((19853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2246 : ((((11306069209 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19853 < q → q < 19861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19861).mp (by decide +kernel))) hgap
  have hprev := s2L_2245
  have hrat : ((11306069209 : ℚ) / 25000000000) ≤ ((18089710633 : ℚ) / 40000000000) + (19861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306069209 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((18089710633 : ℚ) / 40000000000) : ℚ) : ℝ) + ((19861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19861:ℚ)^(-2:ℤ) : ℝ) = ((19861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2247 : ((((452242770893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19861 < q → q < 19867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19867).mp (by decide +kernel))) hgap
  have hprev := s2L_2246
  have hrat : ((452242770893 : ℚ) / 1000000000000) ≤ ((11306069209 : ℚ) / 25000000000) + (19867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242770893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306069209 : ℚ) / 25000000000) : ℚ) : ℝ) + ((19867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19867:ℚ)^(-2:ℤ) : ℝ) = ((19867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2248 : ((((22612138671 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19867 < q → q < 19889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19889).mp (by decide +kernel))) hgap
  have hprev := s2L_2247
  have hrat : ((22612138671 : ℚ) / 50000000000) ≤ ((452242770893 : ℚ) / 1000000000000) + (19889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612138671 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242770893 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19889:ℚ)^(-2:ℤ) : ℝ) = ((19889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2249 : ((((452242775947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19891, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19889 < q → q < 19891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19891).mp (by decide +kernel))) hgap
  have hprev := s2L_2248
  have hrat : ((452242775947 : ℚ) / 1000000000000) ≤ ((22612138671 : ℚ) / 50000000000) + (19891:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242775947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612138671 : ℚ) / 50000000000) : ℚ) : ℝ) + ((19891:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19891:ℚ)^(-2:ℤ) : ℝ) = ((19891:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2250 : ((((113060694617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19913, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19891 < q → q < 19913 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19913).mp (by decide +kernel))) hgap
  have hprev := s2L_2249
  have hrat : ((113060694617 : ℚ) / 250000000000) ≤ ((452242775947 : ℚ) / 1000000000000) + (19913:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060694617 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242775947 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19913:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19913:ℚ)^(-2:ℤ) : ℝ) = ((19913:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2251 : ((((113060695247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19913 < q → q < 19919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19919).mp (by decide +kernel))) hgap
  have hprev := s2L_2250
  have hrat : ((113060695247 : ℚ) / 250000000000) ≤ ((113060694617 : ℚ) / 250000000000) + (19919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060695247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060694617 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19919:ℚ)^(-2:ℤ) : ℝ) = ((19919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2252 : ((((226121391753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19919 < q → q < 19927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19927).mp (by decide +kernel))) hgap
  have hprev := s2L_2251
  have hrat : ((226121391753 : ℚ) / 500000000000) ≤ ((113060695247 : ℚ) / 250000000000) + (19927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121391753 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060695247 : ℚ) / 250000000000) : ℚ) : ℝ) + ((19927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19927:ℚ)^(-2:ℤ) : ℝ) = ((19927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2253 : ((((452242786021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19927 < q → q < 19937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19937).mp (by decide +kernel))) hgap
  have hprev := s2L_2252
  have hrat : ((452242786021 : ℚ) / 1000000000000) ≤ ((226121391753 : ℚ) / 500000000000) + (19937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242786021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121391753 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19937:ℚ)^(-2:ℤ) : ℝ) = ((19937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2254 : ((((452242788533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19937 < q → q < 19949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19949).mp (by decide +kernel))) hgap
  have hprev := s2L_2253
  have hrat : ((452242788533 : ℚ) / 1000000000000) ≤ ((452242786021 : ℚ) / 1000000000000) + (19949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242788533 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242786021 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19949:ℚ)^(-2:ℤ) : ℝ) = ((19949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2255 : ((((226121395521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19949 < q → q < 19961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19961).mp (by decide +kernel))) hgap
  have hprev := s2L_2254
  have hrat : ((226121395521 : ℚ) / 500000000000) ≤ ((452242788533 : ℚ) / 1000000000000) + (19961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121395521 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242788533 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19961:ℚ)^(-2:ℤ) : ℝ) = ((19961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2256 : ((((452242793551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19961 < q → q < 19963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19963).mp (by decide +kernel))) hgap
  have hprev := s2L_2255
  have hrat : ((452242793551 : ℚ) / 1000000000000) ≤ ((226121395521 : ℚ) / 500000000000) + (19963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242793551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121395521 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19963:ℚ)^(-2:ℤ) : ℝ) = ((19963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2257 : ((((452242796057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19963 < q → q < 19973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19973).mp (by decide +kernel))) hgap
  have hprev := s2L_2256
  have hrat : ((452242796057 : ℚ) / 1000000000000) ≤ ((452242793551 : ℚ) / 1000000000000) + (19973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242796057 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242793551 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19973:ℚ)^(-2:ℤ) : ℝ) = ((19973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2258 : ((((226121399281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19973 < q → q < 19979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19979).mp (by decide +kernel))) hgap
  have hprev := s2L_2257
  have hrat : ((226121399281 : ℚ) / 500000000000) ≤ ((452242796057 : ℚ) / 1000000000000) + (19979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121399281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242796057 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((19979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19979:ℚ)^(-2:ℤ) : ℝ) = ((19979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2259 : ((((56530350133 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19991, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19979 < q → q < 19991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19991).mp (by decide +kernel))) hgap
  have hprev := s2L_2258
  have hrat : ((56530350133 : ℚ) / 125000000000) ≤ ((226121399281 : ℚ) / 500000000000) + (19991:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530350133 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121399281 : ℚ) / 500000000000) : ℚ) : ℝ) + ((19991:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19991:ℚ)^(-2:ℤ) : ℝ) = ((19991:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2260 : ((((90448560713 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19991 < q → q < 19993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19993).mp (by decide +kernel))) hgap
  have hprev := s2L_2259
  have hrat : ((90448560713 : ℚ) / 200000000000) ≤ ((56530350133 : ℚ) / 125000000000) + (19993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448560713 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530350133 : ℚ) / 125000000000) : ℚ) : ℝ) + ((19993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19993:ℚ)^(-2:ℤ) : ℝ) = ((19993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2261 : ((((90448561213 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 19997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19993 < q → q < 19997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 19997).mp (by decide +kernel))) hgap
  have hprev := s2L_2260
  have hrat : ((90448561213 : ℚ) / 200000000000) ≤ ((90448560713 : ℚ) / 200000000000) + (19997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448561213 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448560713 : ℚ) / 200000000000) : ℚ) : ℝ) + ((19997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((19997:ℚ)^(-2:ℤ) : ℝ) = ((19997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2262 : ((((226121404281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 19997 < q → q < 20011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20011).mp (by decide +kernel))) hgap
  have hprev := s2L_2261
  have hrat : ((226121404281 : ℚ) / 500000000000) ≤ ((90448561213 : ℚ) / 200000000000) + (20011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121404281 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448561213 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20011:ℚ)^(-2:ℤ) : ℝ) = ((20011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2263 : ((((28265175691 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20021, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20011 < q → q < 20021 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20021).mp (by decide +kernel))) hgap
  have hprev := s2L_2262
  have hrat : ((28265175691 : ℚ) / 62500000000) ≤ ((226121404281 : ℚ) / 500000000000) + (20021:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265175691 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121404281 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20021:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20021:ℚ)^(-2:ℤ) : ℝ) = ((20021:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2264 : ((((9044856271 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20021 < q → q < 20023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20023).mp (by decide +kernel))) hgap
  have hprev := s2L_2263
  have hrat : ((9044856271 : ℚ) / 20000000000) ≤ ((28265175691 : ℚ) / 62500000000) + (20023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044856271 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((28265175691 : ℚ) / 62500000000) : ℚ) : ℝ) + ((20023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20023:ℚ)^(-2:ℤ) : ℝ) = ((20023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2265 : ((((226121408021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20023 < q → q < 20029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20029).mp (by decide +kernel))) hgap
  have hprev := s2L_2264
  have hrat : ((226121408021 : ℚ) / 500000000000) ≤ ((9044856271 : ℚ) / 20000000000) + (20029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121408021 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9044856271 : ℚ) / 20000000000) : ℚ) : ℝ) + ((20029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20029:ℚ)^(-2:ℤ) : ℝ) = ((20029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2266 : ((((45224281853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20029 < q → q < 20047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20047).mp (by decide +kernel))) hgap
  have hprev := s2L_2265
  have hrat : ((45224281853 : ℚ) / 100000000000) ≤ ((226121408021 : ℚ) / 500000000000) + (20047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224281853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121408021 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20047:ℚ)^(-2:ℤ) : ℝ) = ((20047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2267 : ((((452242821017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20047 < q → q < 20051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20051).mp (by decide +kernel))) hgap
  have hprev := s2L_2266
  have hrat : ((452242821017 : ℚ) / 1000000000000) ≤ ((45224281853 : ℚ) / 100000000000) + (20051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242821017 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224281853 : ℚ) / 100000000000) : ℚ) : ℝ) + ((20051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20051:ℚ)^(-2:ℤ) : ℝ) = ((20051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2268 : ((((452242823501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20051 < q → q < 20063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20063).mp (by decide +kernel))) hgap
  have hprev := s2L_2267
  have hrat : ((452242823501 : ℚ) / 1000000000000) ≤ ((452242821017 : ℚ) / 1000000000000) + (20063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242823501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242821017 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20063:ℚ)^(-2:ℤ) : ℝ) = ((20063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2269 : ((((452242825983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20063 < q → q < 20071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20071).mp (by decide +kernel))) hgap
  have hprev := s2L_2268
  have hrat : ((452242825983 : ℚ) / 1000000000000) ≤ ((452242823501 : ℚ) / 1000000000000) + (20071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242825983 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242823501 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20071:ℚ)^(-2:ℤ) : ℝ) = ((20071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2270 : ((((22612141423 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20071 < q → q < 20089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20089).mp (by decide +kernel))) hgap
  have hprev := s2L_2269
  have hrat : ((22612141423 : ℚ) / 50000000000) ≤ ((452242825983 : ℚ) / 1000000000000) + (20089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612141423 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452242825983 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20089:ℚ)^(-2:ℤ) : ℝ) = ((20089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2271 : ((((226121415467 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20089 < q → q < 20101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20101).mp (by decide +kernel))) hgap
  have hprev := s2L_2270
  have hrat : ((226121415467 : ℚ) / 500000000000) ≤ ((22612141423 : ℚ) / 50000000000) + (20101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121415467 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22612141423 : ℚ) / 50000000000) : ℚ) : ℝ) + ((20101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20101:ℚ)^(-2:ℤ) : ℝ) = ((20101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2272 : ((((452242833407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20101 < q → q < 20107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20107).mp (by decide +kernel))) hgap
  have hprev := s2L_2271
  have hrat : ((452242833407 : ℚ) / 1000000000000) ≤ ((226121415467 : ℚ) / 500000000000) + (20107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242833407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121415467 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20107:ℚ)^(-2:ℤ) : ℝ) = ((20107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2273 : ((((226121417939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20107 < q → q < 20113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20113).mp (by decide +kernel))) hgap
  have hprev := s2L_2272
  have hrat : ((226121417939 : ℚ) / 500000000000) ≤ ((452242833407 : ℚ) / 1000000000000) + (20113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121417939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242833407 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20113:ℚ)^(-2:ℤ) : ℝ) = ((20113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2274 : ((((452242838349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20113 < q → q < 20117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20117).mp (by decide +kernel))) hgap
  have hprev := s2L_2273
  have hrat : ((452242838349 : ℚ) / 1000000000000) ≤ ((226121417939 : ℚ) / 500000000000) + (20117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242838349 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121417939 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20117:ℚ)^(-2:ℤ) : ℝ) = ((20117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2275 : ((((226121420409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20117 < q → q < 20123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20123).mp (by decide +kernel))) hgap
  have hprev := s2L_2274
  have hrat : ((226121420409 : ℚ) / 500000000000) ≤ ((452242838349 : ℚ) / 1000000000000) + (20123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121420409 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242838349 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20123:ℚ)^(-2:ℤ) : ℝ) = ((20123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2276 : ((((226121421643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20123 < q → q < 20129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20129).mp (by decide +kernel))) hgap
  have hprev := s2L_2275
  have hrat : ((226121421643 : ℚ) / 500000000000) ≤ ((226121420409 : ℚ) / 500000000000) + (20129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121421643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121420409 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20129:ℚ)^(-2:ℤ) : ℝ) = ((20129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2277 : ((((1808971383 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20129 < q → q < 20143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20143).mp (by decide +kernel))) hgap
  have hprev := s2L_2276
  have hrat : ((1808971383 : ℚ) / 4000000000) ≤ ((226121421643 : ℚ) / 500000000000) + (20143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808971383 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((226121421643 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20143:ℚ)^(-2:ℤ) : ℝ) = ((20143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2278 : ((((452242848213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20143 < q → q < 20147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20147).mp (by decide +kernel))) hgap
  have hprev := s2L_2277
  have hrat : ((452242848213 : ℚ) / 1000000000000) ≤ ((1808971383 : ℚ) / 4000000000) + (20147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242848213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1808971383 : ℚ) / 4000000000) : ℚ) : ℝ) + ((20147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20147:ℚ)^(-2:ℤ) : ℝ) = ((20147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2279 : ((((113060712669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20147 < q → q < 20149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20149).mp (by decide +kernel))) hgap
  have hprev := s2L_2278
  have hrat : ((113060712669 : ℚ) / 250000000000) ≤ ((452242848213 : ℚ) / 1000000000000) + (20149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060712669 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242848213 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20149:ℚ)^(-2:ℤ) : ℝ) = ((20149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2280 : ((((28265178321 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20149 < q → q < 20161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20161).mp (by decide +kernel))) hgap
  have hprev := s2L_2279
  have hrat : ((28265178321 : ℚ) / 62500000000) ≤ ((113060712669 : ℚ) / 250000000000) + (20161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265178321 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113060712669 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20161:ℚ)^(-2:ℤ) : ℝ) = ((20161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2281 : ((((452242855593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20161 < q → q < 20173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20173).mp (by decide +kernel))) hgap
  have hprev := s2L_2280
  have hrat : ((452242855593 : ℚ) / 1000000000000) ≤ ((28265178321 : ℚ) / 62500000000) + (20173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242855593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265178321 : ℚ) / 62500000000) : ℚ) : ℝ) + ((20173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20173:ℚ)^(-2:ℤ) : ℝ) = ((20173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2282 : ((((452242858049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20173 < q → q < 20177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20177).mp (by decide +kernel))) hgap
  have hprev := s2L_2281
  have hrat : ((452242858049 : ℚ) / 1000000000000) ≤ ((452242855593 : ℚ) / 1000000000000) + (20177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242858049 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242855593 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20177:ℚ)^(-2:ℤ) : ℝ) = ((20177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2283 : ((((452242860503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20177 < q → q < 20183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20183).mp (by decide +kernel))) hgap
  have hprev := s2L_2282
  have hrat : ((452242860503 : ℚ) / 1000000000000) ≤ ((452242858049 : ℚ) / 1000000000000) + (20183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242860503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242858049 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20183:ℚ)^(-2:ℤ) : ℝ) = ((20183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2284 : ((((452242862953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20201, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20183 < q → q < 20201 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20201).mp (by decide +kernel))) hgap
  have hprev := s2L_2283
  have hrat : ((452242862953 : ℚ) / 1000000000000) ≤ ((452242860503 : ℚ) / 1000000000000) + (20201:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242862953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242860503 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20201:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20201:ℚ)^(-2:ℤ) : ℝ) = ((20201:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2285 : ((((452242865399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20201 < q → q < 20219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20219).mp (by decide +kernel))) hgap
  have hprev := s2L_2284
  have hrat : ((452242865399 : ℚ) / 1000000000000) ≤ ((452242862953 : ℚ) / 1000000000000) + (20219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242865399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242862953 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20219:ℚ)^(-2:ℤ) : ℝ) = ((20219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2286 : ((((226121433921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20219 < q → q < 20231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20231).mp (by decide +kernel))) hgap
  have hprev := s2L_2285
  have hrat : ((226121433921 : ℚ) / 500000000000) ≤ ((452242865399 : ℚ) / 1000000000000) + (20231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121433921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242865399 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20231:ℚ)^(-2:ℤ) : ℝ) = ((20231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2287 : ((((113060717571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20231 < q → q < 20233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20233).mp (by decide +kernel))) hgap
  have hprev := s2L_2286
  have hrat : ((113060717571 : ℚ) / 250000000000) ≤ ((226121433921 : ℚ) / 500000000000) + (20233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060717571 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121433921 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20233:ℚ)^(-2:ℤ) : ℝ) = ((20233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2288 : ((((226121436361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20233 < q → q < 20249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20249).mp (by decide +kernel))) hgap
  have hprev := s2L_2287
  have hrat : ((226121436361 : ℚ) / 500000000000) ≤ ((113060717571 : ℚ) / 250000000000) + (20249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121436361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060717571 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20249:ℚ)^(-2:ℤ) : ℝ) = ((20249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2289 : ((((226121437579 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20249 < q → q < 20261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20261).mp (by decide +kernel))) hgap
  have hprev := s2L_2288
  have hrat : ((226121437579 : ℚ) / 500000000000) ≤ ((226121436361 : ℚ) / 500000000000) + (20261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121437579 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121436361 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20261:ℚ)^(-2:ℤ) : ℝ) = ((20261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2290 : ((((56530359699 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20261 < q → q < 20269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20269).mp (by decide +kernel))) hgap
  have hprev := s2L_2289
  have hrat : ((56530359699 : ℚ) / 125000000000) ≤ ((226121437579 : ℚ) / 500000000000) + (20269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530359699 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121437579 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20269:ℚ)^(-2:ℤ) : ℝ) = ((20269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2291 : ((((452242880021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20269 < q → q < 20287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20287).mp (by decide +kernel))) hgap
  have hprev := s2L_2290
  have hrat : ((452242880021 : ℚ) / 1000000000000) ≤ ((56530359699 : ℚ) / 125000000000) + (20287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242880021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530359699 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20287:ℚ)^(-2:ℤ) : ℝ) = ((20287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2292 : ((((28265180153 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20287 < q → q < 20297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20297).mp (by decide +kernel))) hgap
  have hprev := s2L_2291
  have hrat : ((28265180153 : ℚ) / 62500000000) ≤ ((452242880021 : ℚ) / 1000000000000) + (20297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265180153 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452242880021 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20297:ℚ)^(-2:ℤ) : ℝ) = ((20297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2293 : ((((452242884869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20297 < q → q < 20323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20323).mp (by decide +kernel))) hgap
  have hprev := s2L_2292
  have hrat : ((452242884869 : ℚ) / 1000000000000) ≤ ((28265180153 : ℚ) / 62500000000) + (20323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242884869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28265180153 : ℚ) / 62500000000) : ℚ) : ℝ) + ((20323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20323:ℚ)^(-2:ℤ) : ℝ) = ((20323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2294 : ((((452242887289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20323 < q → q < 20327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20327).mp (by decide +kernel))) hgap
  have hprev := s2L_2293
  have hrat : ((452242887289 : ℚ) / 1000000000000) ≤ ((452242884869 : ℚ) / 1000000000000) + (20327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242887289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242884869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20327:ℚ)^(-2:ℤ) : ℝ) = ((20327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2295 : ((((452242889707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20327 < q → q < 20333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20333).mp (by decide +kernel))) hgap
  have hprev := s2L_2294
  have hrat : ((452242889707 : ℚ) / 1000000000000) ≤ ((452242887289 : ℚ) / 1000000000000) + (20333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242889707 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242887289 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20333:ℚ)^(-2:ℤ) : ℝ) = ((20333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2296 : ((((452242892123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20333 < q → q < 20341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20341).mp (by decide +kernel))) hgap
  have hprev := s2L_2295
  have hrat : ((452242892123 : ℚ) / 1000000000000) ≤ ((452242889707 : ℚ) / 1000000000000) + (20341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242892123 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242889707 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20341:ℚ)^(-2:ℤ) : ℝ) = ((20341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2297 : ((((226121447269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20341 < q → q < 20347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20347).mp (by decide +kernel))) hgap
  have hprev := s2L_2296
  have hrat : ((226121447269 : ℚ) / 500000000000) ≤ ((452242892123 : ℚ) / 1000000000000) + (20347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121447269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242892123 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20347:ℚ)^(-2:ℤ) : ℝ) = ((20347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2298 : ((((56530362119 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20347 < q → q < 20353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20353).mp (by decide +kernel))) hgap
  have hprev := s2L_2297
  have hrat : ((56530362119 : ℚ) / 125000000000) ≤ ((226121447269 : ℚ) / 500000000000) + (20353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530362119 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226121447269 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20353:ℚ)^(-2:ℤ) : ℝ) = ((20353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2299 : ((((90448579873 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20353 < q → q < 20357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20357).mp (by decide +kernel))) hgap
  have hprev := s2L_2298
  have hrat : ((90448579873 : ℚ) / 200000000000) ≤ ((56530362119 : ℚ) / 125000000000) + (20357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448579873 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56530362119 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20357:ℚ)^(-2:ℤ) : ℝ) = ((20357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2300 : ((((452242901777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20357 < q → q < 20359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20359).mp (by decide +kernel))) hgap
  have hprev := s2L_2299
  have hrat : ((452242901777 : ℚ) / 1000000000000) ≤ ((90448579873 : ℚ) / 200000000000) + (20359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242901777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448579873 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20359:ℚ)^(-2:ℤ) : ℝ) = ((20359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2301 : ((((452242904187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20359 < q → q < 20369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20369).mp (by decide +kernel))) hgap
  have hprev := s2L_2300
  have hrat : ((452242904187 : ℚ) / 1000000000000) ≤ ((452242901777 : ℚ) / 1000000000000) + (20369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242904187 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242901777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20369:ℚ)^(-2:ℤ) : ℝ) = ((20369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2302 : ((((14132590831 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20369 < q → q < 20389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20389).mp (by decide +kernel))) hgap
  have hprev := s2L_2301
  have hrat : ((14132590831 : ℚ) / 31250000000) ≤ ((452242904187 : ℚ) / 1000000000000) + (20389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132590831 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452242904187 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20389:ℚ)^(-2:ℤ) : ℝ) = ((20389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2303 : ((((113060727249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20389 < q → q < 20393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20393).mp (by decide +kernel))) hgap
  have hprev := s2L_2302
  have hrat : ((113060727249 : ℚ) / 250000000000) ≤ ((14132590831 : ℚ) / 31250000000) + (20393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060727249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14132590831 : ℚ) / 31250000000) : ℚ) : ℝ) + ((20393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20393:ℚ)^(-2:ℤ) : ℝ) = ((20393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2304 : ((((452242911399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20393 < q → q < 20399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20399).mp (by decide +kernel))) hgap
  have hprev := s2L_2303
  have hrat : ((452242911399 : ℚ) / 1000000000000) ≤ ((113060727249 : ℚ) / 250000000000) + (20399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242911399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060727249 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20399:ℚ)^(-2:ℤ) : ℝ) = ((20399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2305 : ((((2261214569 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20399 < q → q < 20407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20407).mp (by decide +kernel))) hgap
  have hprev := s2L_2304
  have hrat : ((2261214569 : ℚ) / 5000000000) ≤ ((452242911399 : ℚ) / 1000000000000) + (20407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261214569 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((452242911399 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20407:ℚ)^(-2:ℤ) : ℝ) = ((20407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2306 : ((((2261214581 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20407 < q → q < 20411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20411).mp (by decide +kernel))) hgap
  have hprev := s2L_2305
  have hrat : ((2261214581 : ℚ) / 5000000000) ≤ ((2261214569 : ℚ) / 5000000000) + (20411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261214581 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((2261214569 : ℚ) / 5000000000) : ℚ) : ℝ) + ((20411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20411:ℚ)^(-2:ℤ) : ℝ) = ((20411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2307 : ((((90448583719 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20411 < q → q < 20431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20431).mp (by decide +kernel))) hgap
  have hprev := s2L_2306
  have hrat : ((90448583719 : ℚ) / 200000000000) ≤ ((2261214581 : ℚ) / 5000000000) + (20431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448583719 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((2261214581 : ℚ) / 5000000000) : ℚ) : ℝ) + ((20431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20431:ℚ)^(-2:ℤ) : ℝ) = ((20431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2308 : ((((113060730247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20431 < q → q < 20441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20441).mp (by decide +kernel))) hgap
  have hprev := s2L_2307
  have hrat : ((113060730247 : ℚ) / 250000000000) ≤ ((90448583719 : ℚ) / 200000000000) + (20441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060730247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448583719 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20441:ℚ)^(-2:ℤ) : ℝ) = ((20441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2309 : ((((22612146169 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20441 < q → q < 20443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20443).mp (by decide +kernel))) hgap
  have hprev := s2L_2308
  have hrat : ((22612146169 : ℚ) / 50000000000) ≤ ((113060730247 : ℚ) / 250000000000) + (20443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612146169 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113060730247 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20443:ℚ)^(-2:ℤ) : ℝ) = ((20443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2310 : ((((113060731441 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20443 < q → q < 20477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20477).mp (by decide +kernel))) hgap
  have hprev := s2L_2309
  have hrat : ((113060731441 : ℚ) / 250000000000) ≤ ((22612146169 : ℚ) / 50000000000) + (20477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060731441 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22612146169 : ℚ) / 50000000000) : ℚ) : ℝ) + ((20477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20477:ℚ)^(-2:ℤ) : ℝ) = ((20477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2311 : ((((113060732037 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20477 < q → q < 20479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20479).mp (by decide +kernel))) hgap
  have hprev := s2L_2310
  have hrat : ((113060732037 : ℚ) / 250000000000) ≤ ((113060731441 : ℚ) / 250000000000) + (20479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060732037 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060731441 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20479:ℚ)^(-2:ℤ) : ℝ) = ((20479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2312 : ((((452242930531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20479 < q → q < 20483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20483).mp (by decide +kernel))) hgap
  have hprev := s2L_2311
  have hrat : ((452242930531 : ℚ) / 1000000000000) ≤ ((113060732037 : ℚ) / 250000000000) + (20483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242930531 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060732037 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20483:ℚ)^(-2:ℤ) : ℝ) = ((20483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2313 : ((((113060733227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20507, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20483 < q → q < 20507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20507).mp (by decide +kernel))) hgap
  have hprev := s2L_2312
  have hrat : ((113060733227 : ℚ) / 250000000000) ≤ ((452242930531 : ℚ) / 1000000000000) + (20507:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060733227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452242930531 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20507:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20507:ℚ)^(-2:ℤ) : ℝ) = ((20507:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2314 : ((((90448587057 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20509, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20507 < q → q < 20509 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20509).mp (by decide +kernel))) hgap
  have hprev := s2L_2313
  have hrat : ((90448587057 : ℚ) / 200000000000) ≤ ((113060733227 : ℚ) / 250000000000) + (20509:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448587057 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060733227 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20509:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20509:ℚ)^(-2:ℤ) : ℝ) = ((20509:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2315 : ((((452242937659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20509 < q → q < 20521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20521).mp (by decide +kernel))) hgap
  have hprev := s2L_2314
  have hrat : ((452242937659 : ℚ) / 1000000000000) ≤ ((90448587057 : ℚ) / 200000000000) + (20521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242937659 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448587057 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20521:ℚ)^(-2:ℤ) : ℝ) = ((20521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2316 : ((((45224294003 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20533, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20521 < q → q < 20533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20533).mp (by decide +kernel))) hgap
  have hprev := s2L_2315
  have hrat : ((45224294003 : ℚ) / 100000000000) ≤ ((452242937659 : ℚ) / 1000000000000) + (20533:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224294003 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242937659 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20533:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20533:ℚ)^(-2:ℤ) : ℝ) = ((20533:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2317 : ((((452242942399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20533 < q → q < 20543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20543).mp (by decide +kernel))) hgap
  have hprev := s2L_2316
  have hrat : ((452242942399 : ℚ) / 1000000000000) ≤ ((45224294003 : ℚ) / 100000000000) + (20543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242942399 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224294003 : ℚ) / 100000000000) : ℚ) : ℝ) + ((20543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20543:ℚ)^(-2:ℤ) : ℝ) = ((20543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2318 : ((((452242944767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20543 < q → q < 20549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20549).mp (by decide +kernel))) hgap
  have hprev := s2L_2317
  have hrat : ((452242944767 : ℚ) / 1000000000000) ≤ ((452242942399 : ℚ) / 1000000000000) + (20549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242944767 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242942399 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20549:ℚ)^(-2:ℤ) : ℝ) = ((20549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2319 : ((((226121473567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20549 < q → q < 20551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20551).mp (by decide +kernel))) hgap
  have hprev := s2L_2318
  have hrat : ((226121473567 : ℚ) / 500000000000) ≤ ((452242944767 : ℚ) / 1000000000000) + (20551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121473567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242944767 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20551:ℚ)^(-2:ℤ) : ℝ) = ((20551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2320 : ((((226121474749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20551 < q → q < 20563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20563).mp (by decide +kernel))) hgap
  have hprev := s2L_2319
  have hrat : ((226121474749 : ℚ) / 500000000000) ≤ ((226121473567 : ℚ) / 500000000000) + (20563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121474749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121473567 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20563:ℚ)^(-2:ℤ) : ℝ) = ((20563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2321 : ((((28265184491 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20563 < q → q < 20593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20593).mp (by decide +kernel))) hgap
  have hprev := s2L_2320
  have hrat : ((28265184491 : ℚ) / 62500000000) ≤ ((226121474749 : ℚ) / 500000000000) + (20593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265184491 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121474749 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20593:ℚ)^(-2:ℤ) : ℝ) = ((20593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2322 : ((((113060738553 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20593 < q → q < 20599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20599).mp (by decide +kernel))) hgap
  have hprev := s2L_2321
  have hrat : ((113060738553 : ℚ) / 250000000000) ≤ ((28265184491 : ℚ) / 62500000000) + (20599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060738553 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28265184491 : ℚ) / 62500000000) : ℚ) : ℝ) + ((20599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20599:ℚ)^(-2:ℤ) : ℝ) = ((20599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2323 : ((((90448591313 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20599 < q → q < 20611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20611).mp (by decide +kernel))) hgap
  have hprev := s2L_2322
  have hrat : ((90448591313 : ℚ) / 200000000000) ≤ ((113060738553 : ℚ) / 250000000000) + (20611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448591313 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060738553 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20611:ℚ)^(-2:ℤ) : ℝ) = ((20611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2324 : ((((90448591783 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20611 < q → q < 20627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20627).mp (by decide +kernel))) hgap
  have hprev := s2L_2323
  have hrat : ((90448591783 : ℚ) / 200000000000) ≤ ((90448591313 : ℚ) / 200000000000) + (20627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448591783 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448591313 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20627:ℚ)^(-2:ℤ) : ℝ) = ((20627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2325 : ((((226121480631 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20627 < q → q < 20639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20639).mp (by decide +kernel))) hgap
  have hprev := s2L_2324
  have hrat : ((226121480631 : ℚ) / 500000000000) ≤ ((90448591783 : ℚ) / 200000000000) + (20639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121480631 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448591783 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20639:ℚ)^(-2:ℤ) : ℝ) = ((20639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2326 : ((((452242963609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20639 < q → q < 20641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20641).mp (by decide +kernel))) hgap
  have hprev := s2L_2325
  have hrat : ((452242963609 : ℚ) / 1000000000000) ≤ ((226121480631 : ℚ) / 500000000000) + (20641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242963609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121480631 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20641:ℚ)^(-2:ℤ) : ℝ) = ((20641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2327 : ((((452242965951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20641 < q → q < 20663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20663).mp (by decide +kernel))) hgap
  have hprev := s2L_2326
  have hrat : ((452242965951 : ℚ) / 1000000000000) ≤ ((452242963609 : ℚ) / 1000000000000) + (20663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242965951 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242963609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20663:ℚ)^(-2:ℤ) : ℝ) = ((20663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2328 : ((((452242968289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20663 < q → q < 20681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20681).mp (by decide +kernel))) hgap
  have hprev := s2L_2327
  have hrat : ((452242968289 : ℚ) / 1000000000000) ≤ ((452242965951 : ℚ) / 1000000000000) + (20681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242968289 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242965951 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20681:ℚ)^(-2:ℤ) : ℝ) = ((20681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2329 : ((((220821763 : ℚ) / 488281250) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20681 < q → q < 20693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20693).mp (by decide +kernel))) hgap
  have hprev := s2L_2328
  have hrat : ((220821763 : ℚ) / 488281250) ≤ ((452242968289 : ℚ) / 1000000000000) + (20693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((220821763 : ℚ) / 488281250) : ℚ) : ℝ) ≤ ((((452242968289 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20693:ℚ)^(-2:ℤ) : ℝ) = ((20693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2330 : ((((113060743239 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20707, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20693 < q → q < 20707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20707).mp (by decide +kernel))) hgap
  have hprev := s2L_2329
  have hrat : ((113060743239 : ℚ) / 250000000000) ≤ ((220821763 : ℚ) / 488281250) + (20707:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060743239 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((220821763 : ℚ) / 488281250) : ℚ) : ℝ) + ((20707:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20707:ℚ)^(-2:ℤ) : ℝ) = ((20707:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2331 : ((((90448595057 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20707 < q → q < 20717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20717).mp (by decide +kernel))) hgap
  have hprev := s2L_2330
  have hrat : ((90448595057 : ℚ) / 200000000000) ≤ ((113060743239 : ℚ) / 250000000000) + (20717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448595057 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113060743239 : ℚ) / 250000000000) : ℚ) : ℝ) + ((20717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20717:ℚ)^(-2:ℤ) : ℝ) = ((20717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2332 : ((((226121488807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20717 < q → q < 20719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20719).mp (by decide +kernel))) hgap
  have hprev := s2L_2331
  have hrat : ((226121488807 : ℚ) / 500000000000) ≤ ((90448595057 : ℚ) / 200000000000) + (20719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121488807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448595057 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20719:ℚ)^(-2:ℤ) : ℝ) = ((20719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2333 : ((((22612148997 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20719 < q → q < 20731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20731).mp (by decide +kernel))) hgap
  have hprev := s2L_2332
  have hrat : ((22612148997 : ℚ) / 50000000000) ≤ ((226121488807 : ℚ) / 500000000000) + (20731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612148997 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121488807 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20731:ℚ)^(-2:ℤ) : ℝ) = ((20731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2334 : ((((56530372783 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20731 < q → q < 20743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20743).mp (by decide +kernel))) hgap
  have hprev := s2L_2333
  have hrat : ((56530372783 : ℚ) / 125000000000) ≤ ((22612148997 : ℚ) / 50000000000) + (20743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530372783 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22612148997 : ℚ) / 50000000000) : ℚ) : ℝ) + ((20743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20743:ℚ)^(-2:ℤ) : ℝ) = ((20743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2335 : ((((452242984587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20743 < q → q < 20747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20747).mp (by decide +kernel))) hgap
  have hprev := s2L_2334
  have hrat : ((452242984587 : ℚ) / 1000000000000) ≤ ((56530372783 : ℚ) / 125000000000) + (20747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242984587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530372783 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20747:ℚ)^(-2:ℤ) : ℝ) = ((20747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2336 : ((((452242986909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20747 < q → q < 20749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20749).mp (by decide +kernel))) hgap
  have hprev := s2L_2335
  have hrat : ((452242986909 : ℚ) / 1000000000000) ≤ ((452242984587 : ℚ) / 1000000000000) + (20749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242986909 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452242984587 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20749:ℚ)^(-2:ℤ) : ℝ) = ((20749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2337 : ((((45224298923 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20749 < q → q < 20753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20753).mp (by decide +kernel))) hgap
  have hprev := s2L_2336
  have hrat : ((45224298923 : ℚ) / 100000000000) ≤ ((452242986909 : ℚ) / 1000000000000) + (20753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224298923 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452242986909 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20753:ℚ)^(-2:ℤ) : ℝ) = ((20753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2338 : ((((9044859831 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20753 < q → q < 20759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20759).mp (by decide +kernel))) hgap
  have hprev := s2L_2337
  have hrat : ((9044859831 : ℚ) / 20000000000) ≤ ((45224298923 : ℚ) / 100000000000) + (20759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044859831 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((45224298923 : ℚ) / 100000000000) : ℚ) : ℝ) + ((20759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20759:ℚ)^(-2:ℤ) : ℝ) = ((20759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2339 : ((((452242993867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20771, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20759 < q → q < 20771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20771).mp (by decide +kernel))) hgap
  have hprev := s2L_2338
  have hrat : ((452242993867 : ℚ) / 1000000000000) ≤ ((9044859831 : ℚ) / 20000000000) + (20771:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242993867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044859831 : ℚ) / 20000000000) : ℚ) : ℝ) + ((20771:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20771:ℚ)^(-2:ℤ) : ℝ) = ((20771:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2340 : ((((56530374523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20771 < q → q < 20773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20773).mp (by decide +kernel))) hgap
  have hprev := s2L_2339
  have hrat : ((56530374523 : ℚ) / 125000000000) ≤ ((452242993867 : ℚ) / 1000000000000) + (20773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530374523 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452242993867 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20773:ℚ)^(-2:ℤ) : ℝ) = ((20773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2341 : ((((452242998497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20773 < q → q < 20789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20789).mp (by decide +kernel))) hgap
  have hprev := s2L_2340
  have hrat : ((452242998497 : ℚ) / 1000000000000) ≤ ((56530374523 : ℚ) / 125000000000) + (20789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452242998497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530374523 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20789:ℚ)^(-2:ℤ) : ℝ) = ((20789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2342 : ((((226121500403 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20789 < q → q < 20807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20807).mp (by decide +kernel))) hgap
  have hprev := s2L_2341
  have hrat : ((226121500403 : ℚ) / 500000000000) ≤ ((452242998497 : ℚ) / 1000000000000) + (20807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121500403 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452242998497 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20807:ℚ)^(-2:ℤ) : ℝ) = ((20807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2343 : ((((90448600623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20807 < q → q < 20809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20809).mp (by decide +kernel))) hgap
  have hprev := s2L_2342
  have hrat : ((90448600623 : ℚ) / 200000000000) ≤ ((226121500403 : ℚ) / 500000000000) + (20809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448600623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121500403 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20809:ℚ)^(-2:ℤ) : ℝ) = ((20809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2344 : ((((90448601083 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20849, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20809 < q → q < 20849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20849).mp (by decide +kernel))) hgap
  have hprev := s2L_2343
  have hrat : ((90448601083 : ℚ) / 200000000000) ≤ ((90448600623 : ℚ) / 200000000000) + (20849:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448601083 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448600623 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20849:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20849:ℚ)^(-2:ℤ) : ℝ) = ((20849:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2345 : ((((452243007713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20849 < q → q < 20857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20857).mp (by decide +kernel))) hgap
  have hprev := s2L_2344
  have hrat : ((452243007713 : ℚ) / 1000000000000) ≤ ((90448601083 : ℚ) / 200000000000) + (20857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243007713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448601083 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20857:ℚ)^(-2:ℤ) : ℝ) = ((20857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2346 : ((((56530376251 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20857 < q → q < 20873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20873).mp (by decide +kernel))) hgap
  have hprev := s2L_2345
  have hrat : ((56530376251 : ℚ) / 125000000000) ≤ ((452243007713 : ℚ) / 1000000000000) + (20873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530376251 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243007713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20873:ℚ)^(-2:ℤ) : ℝ) = ((20873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2347 : ((((452243012301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20873 < q → q < 20879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20879).mp (by decide +kernel))) hgap
  have hprev := s2L_2346
  have hrat : ((452243012301 : ℚ) / 1000000000000) ≤ ((56530376251 : ℚ) / 125000000000) + (20879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243012301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530376251 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20879:ℚ)^(-2:ℤ) : ℝ) = ((20879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2348 : ((((452243014593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20879 < q → q < 20887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20887).mp (by decide +kernel))) hgap
  have hprev := s2L_2347
  have hrat : ((452243014593 : ℚ) / 1000000000000) ≤ ((452243012301 : ℚ) / 1000000000000) + (20887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243014593 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243012301 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20887:ℚ)^(-2:ℤ) : ℝ) = ((20887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2349 : ((((226121508441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20897, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20887 < q → q < 20897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20897).mp (by decide +kernel))) hgap
  have hprev := s2L_2348
  have hrat : ((226121508441 : ℚ) / 500000000000) ≤ ((452243014593 : ℚ) / 1000000000000) + (20897:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121508441 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243014593 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20897:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20897:ℚ)^(-2:ℤ) : ℝ) = ((20897:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2350 : ((((452243019171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20899, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20897 < q → q < 20899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20899).mp (by decide +kernel))) hgap
  have hprev := s2L_2349
  have hrat : ((452243019171 : ℚ) / 1000000000000) ≤ ((226121508441 : ℚ) / 500000000000) + (20899:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243019171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121508441 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20899:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20899:ℚ)^(-2:ℤ) : ℝ) = ((20899:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2351 : ((((452243021459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20899 < q → q < 20903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20903).mp (by decide +kernel))) hgap
  have hprev := s2L_2350
  have hrat : ((452243021459 : ℚ) / 1000000000000) ≤ ((452243019171 : ℚ) / 1000000000000) + (20903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243021459 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243019171 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20903:ℚ)^(-2:ℤ) : ℝ) = ((20903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2352 : ((((452243023743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20921, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20903 < q → q < 20921 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20921).mp (by decide +kernel))) hgap
  have hprev := s2L_2351
  have hrat : ((452243023743 : ℚ) / 1000000000000) ≤ ((452243021459 : ℚ) / 1000000000000) + (20921:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243023743 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243021459 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20921:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20921:ℚ)^(-2:ℤ) : ℝ) = ((20921:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2353 : ((((18089721041 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20921 < q → q < 20929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20929).mp (by decide +kernel))) hgap
  have hprev := s2L_2352
  have hrat : ((18089721041 : ℚ) / 40000000000) ≤ ((452243023743 : ℚ) / 1000000000000) + (20929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089721041 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452243023743 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((20929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20929:ℚ)^(-2:ℤ) : ℝ) = ((20929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2354 : ((((90448605661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20929 < q → q < 20939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20939).mp (by decide +kernel))) hgap
  have hprev := s2L_2353
  have hrat : ((90448605661 : ℚ) / 200000000000) ≤ ((18089721041 : ℚ) / 40000000000) + (20939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448605661 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089721041 : ℚ) / 40000000000) : ℚ) : ℝ) + ((20939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20939:ℚ)^(-2:ℤ) : ℝ) = ((20939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2355 : ((((56530378823 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20939 < q → q < 20947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20947).mp (by decide +kernel))) hgap
  have hprev := s2L_2354
  have hrat : ((56530378823 : ℚ) / 125000000000) ≤ ((90448605661 : ℚ) / 200000000000) + (20947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530378823 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90448605661 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20947:ℚ)^(-2:ℤ) : ℝ) = ((20947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2356 : ((((22612151643 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20947 < q → q < 20959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20959).mp (by decide +kernel))) hgap
  have hprev := s2L_2355
  have hrat : ((22612151643 : ℚ) / 50000000000) ≤ ((56530378823 : ℚ) / 125000000000) + (20959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612151643 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56530378823 : ℚ) / 125000000000) : ℚ) : ℝ) + ((20959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20959:ℚ)^(-2:ℤ) : ℝ) = ((20959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2357 : ((((90448607027 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20959 < q → q < 20963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20963).mp (by decide +kernel))) hgap
  have hprev := s2L_2356
  have hrat : ((90448607027 : ℚ) / 200000000000) ≤ ((22612151643 : ℚ) / 50000000000) + (20963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448607027 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22612151643 : ℚ) / 50000000000) : ℚ) : ℝ) + ((20963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20963:ℚ)^(-2:ℤ) : ℝ) = ((20963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2358 : ((((226121518703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20963 < q → q < 20981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20981).mp (by decide +kernel))) hgap
  have hprev := s2L_2357
  have hrat : ((226121518703 : ℚ) / 500000000000) ≤ ((90448607027 : ℚ) / 200000000000) + (20981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121518703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448607027 : ℚ) / 200000000000) : ℚ) : ℝ) + ((20981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20981:ℚ)^(-2:ℤ) : ℝ) = ((20981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2359 : ((((452243039677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 20983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20981 < q → q < 20983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 20983).mp (by decide +kernel))) hgap
  have hprev := s2L_2358
  have hrat : ((452243039677 : ℚ) / 1000000000000) ≤ ((226121518703 : ℚ) / 500000000000) + (20983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243039677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121518703 : ℚ) / 500000000000) : ℚ) : ℝ) + ((20983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((20983:ℚ)^(-2:ℤ) : ℝ) = ((20983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2360 : ((((56530380243 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 20983 < q → q < 21001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21001).mp (by decide +kernel))) hgap
  have hprev := s2L_2359
  have hrat : ((56530380243 : ℚ) / 125000000000) ≤ ((452243039677 : ℚ) / 1000000000000) + (21001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530380243 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243039677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21001:ℚ)^(-2:ℤ) : ℝ) = ((21001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2361 : ((((452243044209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21001 < q → q < 21011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21011).mp (by decide +kernel))) hgap
  have hprev := s2L_2360
  have hrat : ((452243044209 : ℚ) / 1000000000000) ≤ ((56530380243 : ℚ) / 125000000000) + (21011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243044209 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530380243 : ℚ) / 125000000000) : ℚ) : ℝ) + ((21011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21011:ℚ)^(-2:ℤ) : ℝ) = ((21011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2362 : ((((452243046473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21011 < q → q < 21013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21013).mp (by decide +kernel))) hgap
  have hprev := s2L_2361
  have hrat : ((452243046473 : ℚ) / 1000000000000) ≤ ((452243044209 : ℚ) / 1000000000000) + (21013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243046473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243044209 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21013:ℚ)^(-2:ℤ) : ℝ) = ((21013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2363 : ((((14132595273 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21013 < q → q < 21017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21017).mp (by decide +kernel))) hgap
  have hprev := s2L_2362
  have hrat : ((14132595273 : ℚ) / 31250000000) ≤ ((452243046473 : ℚ) / 1000000000000) + (21017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132595273 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452243046473 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21017:ℚ)^(-2:ℤ) : ℝ) = ((21017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2364 : ((((452243050999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21017 < q → q < 21019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21019).mp (by decide +kernel))) hgap
  have hprev := s2L_2363
  have hrat : ((452243050999 : ℚ) / 1000000000000) ≤ ((14132595273 : ℚ) / 31250000000) + (21019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243050999 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132595273 : ℚ) / 31250000000) : ℚ) : ℝ) + ((21019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21019:ℚ)^(-2:ℤ) : ℝ) = ((21019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2365 : ((((452243053261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21023, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21019 < q → q < 21023 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21023).mp (by decide +kernel))) hgap
  have hprev := s2L_2364
  have hrat : ((452243053261 : ℚ) / 1000000000000) ≤ ((452243050999 : ℚ) / 1000000000000) + (21023:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243053261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243050999 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21023:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21023:ℚ)^(-2:ℤ) : ℝ) = ((21023:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2366 : ((((452243055521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21023 < q → q < 21031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21031).mp (by decide +kernel))) hgap
  have hprev := s2L_2365
  have hrat : ((452243055521 : ℚ) / 1000000000000) ≤ ((452243053261 : ℚ) / 1000000000000) + (21031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243055521 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243053261 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21031:ℚ)^(-2:ℤ) : ℝ) = ((21031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2367 : ((((18089722311 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21031 < q → q < 21059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21059).mp (by decide +kernel))) hgap
  have hprev := s2L_2366
  have hrat : ((18089722311 : ℚ) / 40000000000) ≤ ((452243055521 : ℚ) / 1000000000000) + (21059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089722311 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452243055521 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21059:ℚ)^(-2:ℤ) : ℝ) = ((21059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2368 : ((((452243060029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21059 < q → q < 21061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21061).mp (by decide +kernel))) hgap
  have hprev := s2L_2367
  have hrat : ((452243060029 : ℚ) / 1000000000000) ≤ ((18089722311 : ℚ) / 40000000000) + (21061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243060029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089722311 : ℚ) / 40000000000) : ℚ) : ℝ) + ((21061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21061:ℚ)^(-2:ℤ) : ℝ) = ((21061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2369 : ((((226121531141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21061 < q → q < 21067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21067).mp (by decide +kernel))) hgap
  have hprev := s2L_2368
  have hrat : ((226121531141 : ℚ) / 500000000000) ≤ ((452243060029 : ℚ) / 1000000000000) + (21067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121531141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243060029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21067:ℚ)^(-2:ℤ) : ℝ) = ((21067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2370 : ((((45224306453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21067 < q → q < 21089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21089).mp (by decide +kernel))) hgap
  have hprev := s2L_2369
  have hrat : ((45224306453 : ℚ) / 100000000000) ≤ ((226121531141 : ℚ) / 500000000000) + (21089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224306453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121531141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21089:ℚ)^(-2:ℤ) : ℝ) = ((21089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2371 : ((((18089722671 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21089 < q → q < 21101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21101).mp (by decide +kernel))) hgap
  have hprev := s2L_2370
  have hrat : ((18089722671 : ℚ) / 40000000000) ≤ ((45224306453 : ℚ) / 100000000000) + (21101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089722671 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((45224306453 : ℚ) / 100000000000) : ℚ) : ℝ) + ((21101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21101:ℚ)^(-2:ℤ) : ℝ) = ((21101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2372 : ((((452243069019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21101 < q → q < 21107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21107).mp (by decide +kernel))) hgap
  have hprev := s2L_2371
  have hrat : ((452243069019 : ℚ) / 1000000000000) ≤ ((18089722671 : ℚ) / 40000000000) + (21107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243069019 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089722671 : ℚ) / 40000000000) : ℚ) : ℝ) + ((21107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21107:ℚ)^(-2:ℤ) : ℝ) = ((21107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2373 : ((((22612153563 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21107 < q → q < 21121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21121).mp (by decide +kernel))) hgap
  have hprev := s2L_2372
  have hrat : ((22612153563 : ℚ) / 50000000000) ≤ ((452243069019 : ℚ) / 1000000000000) + (21121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612153563 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452243069019 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21121:ℚ)^(-2:ℤ) : ℝ) = ((21121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2374 : ((((452243073497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21121 < q → q < 21139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21139).mp (by decide +kernel))) hgap
  have hprev := s2L_2373
  have hrat : ((452243073497 : ℚ) / 1000000000000) ≤ ((22612153563 : ℚ) / 50000000000) + (21139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243073497 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22612153563 : ℚ) / 50000000000) : ℚ) : ℝ) + ((21139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21139:ℚ)^(-2:ℤ) : ℝ) = ((21139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2375 : ((((226121537867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21139 < q → q < 21143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21143).mp (by decide +kernel))) hgap
  have hprev := s2L_2374
  have hrat : ((226121537867 : ℚ) / 500000000000) ≤ ((452243073497 : ℚ) / 1000000000000) + (21143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121537867 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243073497 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21143:ℚ)^(-2:ℤ) : ℝ) = ((21143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2376 : ((((452243077969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21143 < q → q < 21149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21149).mp (by decide +kernel))) hgap
  have hprev := s2L_2375
  have hrat : ((452243077969 : ℚ) / 1000000000000) ≤ ((226121537867 : ℚ) / 500000000000) + (21149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243077969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121537867 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21149:ℚ)^(-2:ℤ) : ℝ) = ((21149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2377 : ((((452243080203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21149 < q → q < 21157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21157).mp (by decide +kernel))) hgap
  have hprev := s2L_2376
  have hrat : ((452243080203 : ℚ) / 1000000000000) ≤ ((452243077969 : ℚ) / 1000000000000) + (21157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243080203 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243077969 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21157:ℚ)^(-2:ℤ) : ℝ) = ((21157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2378 : ((((90448616487 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21157 < q → q < 21163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21163).mp (by decide +kernel))) hgap
  have hprev := s2L_2377
  have hrat : ((90448616487 : ℚ) / 200000000000) ≤ ((452243080203 : ℚ) / 1000000000000) + (21163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448616487 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243080203 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21163:ℚ)^(-2:ℤ) : ℝ) = ((21163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2379 : ((((226121542333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21163 < q → q < 21169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21169).mp (by decide +kernel))) hgap
  have hprev := s2L_2378
  have hrat : ((226121542333 : ℚ) / 500000000000) ≤ ((90448616487 : ℚ) / 200000000000) + (21169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121542333 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448616487 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21169:ℚ)^(-2:ℤ) : ℝ) = ((21169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2380 : ((((90448617379 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21169 < q → q < 21179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21179).mp (by decide +kernel))) hgap
  have hprev := s2L_2379
  have hrat : ((90448617379 : ℚ) / 200000000000) ≤ ((226121542333 : ℚ) / 500000000000) + (21179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448617379 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121542333 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21179:ℚ)^(-2:ℤ) : ℝ) = ((21179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2381 : ((((226121544561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21179 < q → q < 21187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21187).mp (by decide +kernel))) hgap
  have hprev := s2L_2380
  have hrat : ((226121544561 : ℚ) / 500000000000) ≤ ((90448617379 : ℚ) / 200000000000) + (21187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121544561 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448617379 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21187:ℚ)^(-2:ℤ) : ℝ) = ((21187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2382 : ((((113060772837 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21187 < q → q < 21191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21191).mp (by decide +kernel))) hgap
  have hprev := s2L_2381
  have hrat : ((113060772837 : ℚ) / 250000000000) ≤ ((226121544561 : ℚ) / 500000000000) + (21191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060772837 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121544561 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21191:ℚ)^(-2:ℤ) : ℝ) = ((21191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2383 : ((((226121546787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21191 < q → q < 21193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21193).mp (by decide +kernel))) hgap
  have hprev := s2L_2382
  have hrat : ((226121546787 : ℚ) / 500000000000) ≤ ((113060772837 : ℚ) / 250000000000) + (21193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121546787 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060772837 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21193:ℚ)^(-2:ℤ) : ℝ) = ((21193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2384 : ((((113060773949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21193 < q → q < 21211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21211).mp (by decide +kernel))) hgap
  have hprev := s2L_2383
  have hrat : ((113060773949 : ℚ) / 250000000000) ≤ ((226121546787 : ℚ) / 500000000000) + (21211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060773949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121546787 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21211:ℚ)^(-2:ℤ) : ℝ) = ((21211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2385 : ((((14132596813 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21211 < q → q < 21221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21221).mp (by decide +kernel))) hgap
  have hprev := s2L_2384
  have hrat : ((14132596813 : ℚ) / 31250000000) ≤ ((113060773949 : ℚ) / 250000000000) + (21221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132596813 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113060773949 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21221:ℚ)^(-2:ℤ) : ℝ) = ((21221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2386 : ((((90448620047 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21221 < q → q < 21227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21227).mp (by decide +kernel))) hgap
  have hprev := s2L_2385
  have hrat : ((90448620047 : ℚ) / 200000000000) ≤ ((14132596813 : ℚ) / 31250000000) + (21227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448620047 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14132596813 : ℚ) / 31250000000) : ℚ) : ℝ) + ((21227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21227:ℚ)^(-2:ℤ) : ℝ) = ((21227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2387 : ((((9044862049 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21227 < q → q < 21247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21247).mp (by decide +kernel))) hgap
  have hprev := s2L_2386
  have hrat : ((9044862049 : ℚ) / 20000000000) ≤ ((90448620047 : ℚ) / 200000000000) + (21247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044862049 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((90448620047 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21247:ℚ)^(-2:ℤ) : ℝ) = ((21247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2388 : ((((22612155233 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21247 < q → q < 21269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21269).mp (by decide +kernel))) hgap
  have hprev := s2L_2387
  have hrat : ((22612155233 : ℚ) / 50000000000) ≤ ((9044862049 : ℚ) / 20000000000) + (21269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612155233 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((9044862049 : ℚ) / 20000000000) : ℚ) : ℝ) + ((21269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21269:ℚ)^(-2:ℤ) : ℝ) = ((21269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2389 : ((((113060776717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21269 < q → q < 21277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21277).mp (by decide +kernel))) hgap
  have hprev := s2L_2388
  have hrat : ((113060776717 : ℚ) / 250000000000) ≤ ((22612155233 : ℚ) / 50000000000) + (21277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060776717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22612155233 : ℚ) / 50000000000) : ℚ) : ℝ) + ((21277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21277:ℚ)^(-2:ℤ) : ℝ) = ((21277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2390 : ((((18089724363 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21277 < q → q < 21283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21283).mp (by decide +kernel))) hgap
  have hprev := s2L_2389
  have hrat : ((18089724363 : ℚ) / 40000000000) ≤ ((113060776717 : ℚ) / 250000000000) + (21283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089724363 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113060776717 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21283:ℚ)^(-2:ℤ) : ℝ) = ((21283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2391 : ((((113060777819 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21283 < q → q < 21313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21313).mp (by decide +kernel))) hgap
  have hprev := s2L_2390
  have hrat : ((113060777819 : ℚ) / 250000000000) ≤ ((18089724363 : ℚ) / 40000000000) + (21313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060777819 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((18089724363 : ℚ) / 40000000000) : ℚ) : ℝ) + ((21313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21313:ℚ)^(-2:ℤ) : ℝ) = ((21313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2392 : ((((113060778369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21313 < q → q < 21317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21317).mp (by decide +kernel))) hgap
  have hprev := s2L_2391
  have hrat : ((113060778369 : ℚ) / 250000000000) ≤ ((113060777819 : ℚ) / 250000000000) + (21317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060778369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060777819 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21317:ℚ)^(-2:ℤ) : ℝ) = ((21317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2393 : ((((113060778919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21317 < q → q < 21319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21319).mp (by decide +kernel))) hgap
  have hprev := s2L_2392
  have hrat : ((113060778919 : ℚ) / 250000000000) ≤ ((113060778369 : ℚ) / 250000000000) + (21319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060778919 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113060778369 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21319:ℚ)^(-2:ℤ) : ℝ) = ((21319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2394 : ((((3617944943 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21319 < q → q < 21323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21323).mp (by decide +kernel))) hgap
  have hprev := s2L_2393
  have hrat : ((3617944943 : ℚ) / 8000000000) ≤ ((113060778919 : ℚ) / 250000000000) + (21323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3617944943 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((113060778919 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21323:ℚ)^(-2:ℤ) : ℝ) = ((21323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2395 : ((((45224312007 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21323 < q → q < 21341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21341).mp (by decide +kernel))) hgap
  have hprev := s2L_2394
  have hrat : ((45224312007 : ℚ) / 100000000000) ≤ ((3617944943 : ℚ) / 8000000000) + (21341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224312007 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((3617944943 : ℚ) / 8000000000) : ℚ) : ℝ) + ((21341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21341:ℚ)^(-2:ℤ) : ℝ) = ((21341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2396 : ((((56530390283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21341 < q → q < 21347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21347).mp (by decide +kernel))) hgap
  have hprev := s2L_2395
  have hrat : ((56530390283 : ℚ) / 125000000000) ≤ ((45224312007 : ℚ) / 100000000000) + (21347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530390283 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45224312007 : ℚ) / 100000000000) : ℚ) : ℝ) + ((21347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21347:ℚ)^(-2:ℤ) : ℝ) = ((21347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2397 : ((((113060781113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21347 < q → q < 21377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21377).mp (by decide +kernel))) hgap
  have hprev := s2L_2396
  have hrat : ((113060781113 : ℚ) / 250000000000) ≤ ((56530390283 : ℚ) / 125000000000) + (21377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060781113 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530390283 : ℚ) / 125000000000) : ℚ) : ℝ) + ((21377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21377:ℚ)^(-2:ℤ) : ℝ) = ((21377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2398 : ((((452243126639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21377 < q → q < 21379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21379).mp (by decide +kernel))) hgap
  have hprev := s2L_2397
  have hrat : ((452243126639 : ℚ) / 1000000000000) ≤ ((113060781113 : ℚ) / 250000000000) + (21379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243126639 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060781113 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21379:ℚ)^(-2:ℤ) : ℝ) = ((21379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2399 : ((((226121564413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21379 < q → q < 21383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21383).mp (by decide +kernel))) hgap
  have hprev := s2L_2398
  have hrat : ((226121564413 : ℚ) / 500000000000) ≤ ((452243126639 : ℚ) / 1000000000000) + (21383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121564413 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243126639 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21383:ℚ)^(-2:ℤ) : ℝ) = ((21383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2400 : ((((452243131011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21383 < q → q < 21391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21391).mp (by decide +kernel))) hgap
  have hprev := s2L_2399
  have hrat : ((452243131011 : ℚ) / 1000000000000) ≤ ((226121564413 : ℚ) / 500000000000) + (21391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243131011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121564413 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21391:ℚ)^(-2:ℤ) : ℝ) = ((21391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2401 : ((((90448626639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21391 < q → q < 21397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21397).mp (by decide +kernel))) hgap
  have hprev := s2L_2400
  have hrat : ((90448626639 : ℚ) / 200000000000) ≤ ((452243131011 : ℚ) / 1000000000000) + (21397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448626639 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243131011 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21397:ℚ)^(-2:ℤ) : ℝ) = ((21397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2402 : ((((226121567689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21397 < q → q < 21401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21401).mp (by decide +kernel))) hgap
  have hprev := s2L_2401
  have hrat : ((226121567689 : ℚ) / 500000000000) ≤ ((90448626639 : ℚ) / 200000000000) + (21401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121567689 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448626639 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21401:ℚ)^(-2:ℤ) : ℝ) = ((21401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2403 : ((((11306078439 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21401 < q → q < 21407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21407).mp (by decide +kernel))) hgap
  have hprev := s2L_2402
  have hrat : ((11306078439 : ℚ) / 25000000000) ≤ ((226121567689 : ℚ) / 500000000000) + (21407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306078439 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226121567689 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21407:ℚ)^(-2:ℤ) : ℝ) = ((21407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2404 : ((((452243139739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21407 < q → q < 21419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21419).mp (by decide +kernel))) hgap
  have hprev := s2L_2403
  have hrat : ((452243139739 : ℚ) / 1000000000000) ≤ ((11306078439 : ℚ) / 25000000000) + (21419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243139739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306078439 : ℚ) / 25000000000) : ℚ) : ℝ) + ((21419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21419:ℚ)^(-2:ℤ) : ℝ) = ((21419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2405 : ((((90448628383 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21419 < q → q < 21433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21433).mp (by decide +kernel))) hgap
  have hprev := s2L_2404
  have hrat : ((90448628383 : ℚ) / 200000000000) ≤ ((452243139739 : ℚ) / 1000000000000) + (21433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448628383 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243139739 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21433:ℚ)^(-2:ℤ) : ℝ) = ((21433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2406 : ((((113060786021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21433 < q → q < 21467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21467).mp (by decide +kernel))) hgap
  have hprev := s2L_2405
  have hrat : ((113060786021 : ℚ) / 250000000000) ≤ ((90448628383 : ℚ) / 200000000000) + (21467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060786021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448628383 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21467:ℚ)^(-2:ℤ) : ℝ) = ((21467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2407 : ((((452243146251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21467 < q → q < 21481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21481).mp (by decide +kernel))) hgap
  have hprev := s2L_2406
  have hrat : ((452243146251 : ℚ) / 1000000000000) ≤ ((113060786021 : ℚ) / 250000000000) + (21481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243146251 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060786021 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21481:ℚ)^(-2:ℤ) : ℝ) = ((21481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2408 : ((((3533149597 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21481 < q → q < 21487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21487).mp (by decide +kernel))) hgap
  have hprev := s2L_2407
  have hrat : ((3533149597 : ℚ) / 7812500000) ≤ ((452243146251 : ℚ) / 1000000000000) + (21487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533149597 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((452243146251 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21487:ℚ)^(-2:ℤ) : ℝ) = ((21487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2409 : ((((452243150581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21487 < q → q < 21491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21491).mp (by decide +kernel))) hgap
  have hprev := s2L_2408
  have hrat : ((452243150581 : ℚ) / 1000000000000) ≤ ((3533149597 : ℚ) / 7812500000) + (21491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243150581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3533149597 : ℚ) / 7812500000) : ℚ) : ℝ) + ((21491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21491:ℚ)^(-2:ℤ) : ℝ) = ((21491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2410 : ((((90448630549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21493, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21491 < q → q < 21493 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21493).mp (by decide +kernel))) hgap
  have hprev := s2L_2409
  have hrat : ((90448630549 : ℚ) / 200000000000) ≤ ((452243150581 : ℚ) / 1000000000000) + (21493:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448630549 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243150581 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21493:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21493:ℚ)^(-2:ℤ) : ℝ) = ((21493:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2411 : ((((113060788727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21493 < q → q < 21499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21499).mp (by decide +kernel))) hgap
  have hprev := s2L_2410
  have hrat : ((113060788727 : ℚ) / 250000000000) ≤ ((90448630549 : ℚ) / 200000000000) + (21499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060788727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448630549 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21499:ℚ)^(-2:ℤ) : ℝ) = ((21499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2412 : ((((45224315707 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21499 < q → q < 21503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21503).mp (by decide +kernel))) hgap
  have hprev := s2L_2411
  have hrat : ((45224315707 : ℚ) / 100000000000) ≤ ((113060788727 : ℚ) / 250000000000) + (21503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224315707 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((113060788727 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21503:ℚ)^(-2:ℤ) : ℝ) = ((21503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2413 : ((((452243159229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21503 < q → q < 21517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21517).mp (by decide +kernel))) hgap
  have hprev := s2L_2412
  have hrat : ((452243159229 : ℚ) / 1000000000000) ≤ ((45224315707 : ℚ) / 100000000000) + (21517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243159229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45224315707 : ℚ) / 100000000000) : ℚ) : ℝ) + ((21517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21517:ℚ)^(-2:ℤ) : ℝ) = ((21517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2414 : ((((113060790347 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21517 < q → q < 21521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21521).mp (by decide +kernel))) hgap
  have hprev := s2L_2413
  have hrat : ((113060790347 : ℚ) / 250000000000) ≤ ((452243159229 : ℚ) / 1000000000000) + (21521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060790347 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243159229 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21521:ℚ)^(-2:ℤ) : ℝ) = ((21521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2415 : ((((226121581773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21521 < q → q < 21523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21523).mp (by decide +kernel))) hgap
  have hprev := s2L_2414
  have hrat : ((226121581773 : ℚ) / 500000000000) ≤ ((113060790347 : ℚ) / 250000000000) + (21523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121581773 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060790347 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21523:ℚ)^(-2:ℤ) : ℝ) = ((21523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2416 : ((((452243165703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21523 < q → q < 21529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21529).mp (by decide +kernel))) hgap
  have hprev := s2L_2415
  have hrat : ((452243165703 : ℚ) / 1000000000000) ≤ ((226121581773 : ℚ) / 500000000000) + (21529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243165703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121581773 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21529:ℚ)^(-2:ℤ) : ℝ) = ((21529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2417 : ((((226121583927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21529 < q → q < 21557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21557).mp (by decide +kernel))) hgap
  have hprev := s2L_2416
  have hrat : ((226121583927 : ℚ) / 500000000000) ≤ ((452243165703 : ℚ) / 1000000000000) + (21557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121583927 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243165703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21557:ℚ)^(-2:ℤ) : ℝ) = ((21557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2418 : ((((90448634001 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21557 < q → q < 21559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21559).mp (by decide +kernel))) hgap
  have hprev := s2L_2417
  have hrat : ((90448634001 : ℚ) / 200000000000) ≤ ((226121583927 : ℚ) / 500000000000) + (21559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448634001 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121583927 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21559:ℚ)^(-2:ℤ) : ℝ) = ((21559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2419 : ((((90448634431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21559 < q → q < 21563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21563).mp (by decide +kernel))) hgap
  have hprev := s2L_2418
  have hrat : ((90448634431 : ℚ) / 200000000000) ≤ ((90448634001 : ℚ) / 200000000000) + (21563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448634431 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90448634001 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21563:ℚ)^(-2:ℤ) : ℝ) = ((21563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2420 : ((((14132599197 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21563 < q → q < 21569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21569).mp (by decide +kernel))) hgap
  have hprev := s2L_2419
  have hrat : ((14132599197 : ℚ) / 31250000000) ≤ ((90448634431 : ℚ) / 200000000000) + (21569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132599197 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((90448634431 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21569:ℚ)^(-2:ℤ) : ℝ) = ((21569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2421 : ((((452243176451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21569 < q → q < 21577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21577).mp (by decide +kernel))) hgap
  have hprev := s2L_2420
  have hrat : ((452243176451 : ℚ) / 1000000000000) ≤ ((14132599197 : ℚ) / 31250000000) + (21577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243176451 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132599197 : ℚ) / 31250000000) : ℚ) : ℝ) + ((21577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21577:ℚ)^(-2:ℤ) : ℝ) = ((21577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2422 : ((((113060794649 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21577 < q → q < 21587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21587).mp (by decide +kernel))) hgap
  have hprev := s2L_2421
  have hrat : ((113060794649 : ℚ) / 250000000000) ≤ ((452243176451 : ℚ) / 1000000000000) + (21587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060794649 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243176451 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21587:ℚ)^(-2:ℤ) : ℝ) = ((21587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2423 : ((((452243180741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21589, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21587 < q → q < 21589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21589).mp (by decide +kernel))) hgap
  have hprev := s2L_2422
  have hrat : ((452243180741 : ℚ) / 1000000000000) ≤ ((113060794649 : ℚ) / 250000000000) + (21589:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243180741 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060794649 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21589:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21589:ℚ)^(-2:ℤ) : ℝ) = ((21589:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2424 : ((((113060795721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21589 < q → q < 21599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21599).mp (by decide +kernel))) hgap
  have hprev := s2L_2423
  have hrat : ((113060795721 : ℚ) / 250000000000) ≤ ((452243180741 : ℚ) / 1000000000000) + (21599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060795721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243180741 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21599:ℚ)^(-2:ℤ) : ℝ) = ((21599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2425 : ((((452243185027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21599 < q → q < 21601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21601).mp (by decide +kernel))) hgap
  have hprev := s2L_2424
  have hrat : ((452243185027 : ℚ) / 1000000000000) ≤ ((113060795721 : ℚ) / 250000000000) + (21601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243185027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060795721 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21601:ℚ)^(-2:ℤ) : ℝ) = ((21601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2426 : ((((14132599599 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21601 < q → q < 21611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21611).mp (by decide +kernel))) hgap
  have hprev := s2L_2425
  have hrat : ((14132599599 : ℚ) / 31250000000) ≤ ((452243185027 : ℚ) / 1000000000000) + (21611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132599599 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452243185027 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21611:ℚ)^(-2:ℤ) : ℝ) = ((21611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2427 : ((((113060797327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21611 < q → q < 21613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21613).mp (by decide +kernel))) hgap
  have hprev := s2L_2426
  have hrat : ((113060797327 : ℚ) / 250000000000) ≤ ((14132599599 : ℚ) / 31250000000) + (21613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060797327 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14132599599 : ℚ) / 31250000000) : ℚ) : ℝ) + ((21613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21613:ℚ)^(-2:ℤ) : ℝ) = ((21613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2428 : ((((452243191447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21613 < q → q < 21617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21617).mp (by decide +kernel))) hgap
  have hprev := s2L_2427
  have hrat : ((452243191447 : ℚ) / 1000000000000) ≤ ((113060797327 : ℚ) / 250000000000) + (21617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243191447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060797327 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21617:ℚ)^(-2:ℤ) : ℝ) = ((21617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2429 : ((((452243193581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21617 < q → q < 21647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21647).mp (by decide +kernel))) hgap
  have hprev := s2L_2428
  have hrat : ((452243193581 : ℚ) / 1000000000000) ≤ ((452243191447 : ℚ) / 1000000000000) + (21647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243193581 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243191447 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21647:ℚ)^(-2:ℤ) : ℝ) = ((21647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2430 : ((((226121597857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21647 < q → q < 21649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21649).mp (by decide +kernel))) hgap
  have hprev := s2L_2429
  have hrat : ((226121597857 : ℚ) / 500000000000) ≤ ((452243193581 : ℚ) / 1000000000000) + (21649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121597857 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243193581 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21649:ℚ)^(-2:ℤ) : ℝ) = ((21649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2431 : ((((90448639569 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21649 < q → q < 21661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21661).mp (by decide +kernel))) hgap
  have hprev := s2L_2430
  have hrat : ((90448639569 : ℚ) / 200000000000) ≤ ((226121597857 : ℚ) / 500000000000) + (21661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448639569 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121597857 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21661:ℚ)^(-2:ℤ) : ℝ) = ((21661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2432 : ((((452243199973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21661 < q → q < 21673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21673).mp (by decide +kernel))) hgap
  have hprev := s2L_2431
  have hrat : ((452243199973 : ℚ) / 1000000000000) ≤ ((90448639569 : ℚ) / 200000000000) + (21673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243199973 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448639569 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21673:ℚ)^(-2:ℤ) : ℝ) = ((21673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2433 : ((((452243202099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21673 < q → q < 21683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21683).mp (by decide +kernel))) hgap
  have hprev := s2L_2432
  have hrat : ((452243202099 : ℚ) / 1000000000000) ≤ ((452243199973 : ℚ) / 1000000000000) + (21683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243202099 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243199973 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21683:ℚ)^(-2:ℤ) : ℝ) = ((21683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2434 : ((((226121602111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21683 < q → q < 21701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21701).mp (by decide +kernel))) hgap
  have hprev := s2L_2433
  have hrat : ((226121602111 : ℚ) / 500000000000) ≤ ((452243202099 : ℚ) / 1000000000000) + (21701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121602111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243202099 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21701:ℚ)^(-2:ℤ) : ℝ) = ((21701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2435 : ((((452243206343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21701 < q → q < 21713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21713).mp (by decide +kernel))) hgap
  have hprev := s2L_2434
  have hrat : ((452243206343 : ℚ) / 1000000000000) ≤ ((226121602111 : ℚ) / 500000000000) + (21713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243206343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121602111 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21713:ℚ)^(-2:ℤ) : ℝ) = ((21713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2436 : ((((452243208461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21713 < q → q < 21727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21727).mp (by decide +kernel))) hgap
  have hprev := s2L_2435
  have hrat : ((452243208461 : ℚ) / 1000000000000) ≤ ((452243206343 : ℚ) / 1000000000000) + (21727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243208461 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243206343 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21727:ℚ)^(-2:ℤ) : ℝ) = ((21727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2437 : ((((452243210577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21727 < q → q < 21737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21737).mp (by decide +kernel))) hgap
  have hprev := s2L_2436
  have hrat : ((452243210577 : ℚ) / 1000000000000) ≤ ((452243208461 : ℚ) / 1000000000000) + (21737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243210577 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243208461 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21737:ℚ)^(-2:ℤ) : ℝ) = ((21737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2438 : ((((452243212693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21737 < q → q < 21739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21739).mp (by decide +kernel))) hgap
  have hprev := s2L_2437
  have hrat : ((452243212693 : ℚ) / 1000000000000) ≤ ((452243210577 : ℚ) / 1000000000000) + (21739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243212693 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243210577 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21739:ℚ)^(-2:ℤ) : ℝ) = ((21739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2439 : ((((226121607403 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21751, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21739 < q → q < 21751 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21751).mp (by decide +kernel))) hgap
  have hprev := s2L_2438
  have hrat : ((226121607403 : ℚ) / 500000000000) ≤ ((452243212693 : ℚ) / 1000000000000) + (21751:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121607403 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243212693 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21751:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21751:ℚ)^(-2:ℤ) : ℝ) = ((21751:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2440 : ((((226121608459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21751 < q → q < 21757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21757).mp (by decide +kernel))) hgap
  have hprev := s2L_2439
  have hrat : ((226121608459 : ℚ) / 500000000000) ≤ ((226121607403 : ℚ) / 500000000000) + (21757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121608459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121607403 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21757:ℚ)^(-2:ℤ) : ℝ) = ((21757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2441 : ((((113060804757 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21757 < q → q < 21767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21767).mp (by decide +kernel))) hgap
  have hprev := s2L_2440
  have hrat : ((113060804757 : ℚ) / 250000000000) ≤ ((226121608459 : ℚ) / 500000000000) + (21767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060804757 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226121608459 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21767:ℚ)^(-2:ℤ) : ℝ) = ((21767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2442 : ((((452243221137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21773, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21767 < q → q < 21773 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21773).mp (by decide +kernel))) hgap
  have hprev := s2L_2441
  have hrat : ((452243221137 : ℚ) / 1000000000000) ≤ ((113060804757 : ℚ) / 250000000000) + (21773:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243221137 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060804757 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21773:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21773:ℚ)^(-2:ℤ) : ℝ) = ((21773:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2443 : ((((452243223243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21773 < q → q < 21787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21787).mp (by decide +kernel))) hgap
  have hprev := s2L_2442
  have hrat : ((452243223243 : ℚ) / 1000000000000) ≤ ((452243221137 : ℚ) / 1000000000000) + (21787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243223243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243221137 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21787:ℚ)^(-2:ℤ) : ℝ) = ((21787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2444 : ((((452243225347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21787 < q → q < 21799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21799).mp (by decide +kernel))) hgap
  have hprev := s2L_2443
  have hrat : ((452243225347 : ℚ) / 1000000000000) ≤ ((452243223243 : ℚ) / 1000000000000) + (21799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243225347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243223243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21799:ℚ)^(-2:ℤ) : ℝ) = ((21799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2445 : ((((9044864549 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21799 < q → q < 21803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21803).mp (by decide +kernel))) hgap
  have hprev := s2L_2444
  have hrat : ((9044864549 : ℚ) / 20000000000) ≤ ((452243225347 : ℚ) / 1000000000000) + (21803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044864549 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452243225347 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21803:ℚ)^(-2:ℤ) : ℝ) = ((21803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2446 : ((((9044864591 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21803 < q → q < 21817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21817).mp (by decide +kernel))) hgap
  have hprev := s2L_2445
  have hrat : ((9044864591 : ℚ) / 20000000000) ≤ ((9044864549 : ℚ) / 20000000000) + (21817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044864591 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((9044864549 : ℚ) / 20000000000) : ℚ) : ℝ) + ((21817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21817:ℚ)^(-2:ℤ) : ℝ) = ((21817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2447 : ((((9044864633 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21817 < q → q < 21821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21821).mp (by decide +kernel))) hgap
  have hprev := s2L_2446
  have hrat : ((9044864633 : ℚ) / 20000000000) ≤ ((9044864591 : ℚ) / 20000000000) + (21821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044864633 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((9044864591 : ℚ) / 20000000000) : ℚ) : ℝ) + ((21821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21821:ℚ)^(-2:ℤ) : ℝ) = ((21821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2448 : ((((226121616873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21821 < q → q < 21839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21839).mp (by decide +kernel))) hgap
  have hprev := s2L_2447
  have hrat : ((226121616873 : ℚ) / 500000000000) ≤ ((9044864633 : ℚ) / 20000000000) + (21839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121616873 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((9044864633 : ℚ) / 20000000000) : ℚ) : ℝ) + ((21839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21839:ℚ)^(-2:ℤ) : ℝ) = ((21839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2449 : ((((226121617921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21839 < q → q < 21841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21841).mp (by decide +kernel))) hgap
  have hprev := s2L_2448
  have hrat : ((226121617921 : ℚ) / 500000000000) ≤ ((226121616873 : ℚ) / 500000000000) + (21841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121617921 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121616873 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21841:ℚ)^(-2:ℤ) : ℝ) = ((21841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2450 : ((((28265202371 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21841 < q → q < 21851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21851).mp (by decide +kernel))) hgap
  have hprev := s2L_2449
  have hrat : ((28265202371 : ℚ) / 62500000000) ≤ ((226121617921 : ℚ) / 500000000000) + (21851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28265202371 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226121617921 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21851:ℚ)^(-2:ℤ) : ℝ) = ((21851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2451 : ((((113060810007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21851 < q → q < 21859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21859).mp (by decide +kernel))) hgap
  have hprev := s2L_2450
  have hrat : ((113060810007 : ℚ) / 250000000000) ≤ ((28265202371 : ℚ) / 62500000000) + (21859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060810007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28265202371 : ℚ) / 62500000000) : ℚ) : ℝ) + ((21859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21859:ℚ)^(-2:ℤ) : ℝ) = ((21859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2452 : ((((11306081053 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21859 < q → q < 21863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21863).mp (by decide +kernel))) hgap
  have hprev := s2L_2451
  have hrat : ((11306081053 : ℚ) / 25000000000) ≤ ((113060810007 : ℚ) / 250000000000) + (21863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306081053 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((113060810007 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21863:ℚ)^(-2:ℤ) : ℝ) = ((21863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2453 : ((((45224324421 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21863 < q → q < 21871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21871).mp (by decide +kernel))) hgap
  have hprev := s2L_2452
  have hrat : ((45224324421 : ℚ) / 100000000000) ≤ ((11306081053 : ℚ) / 25000000000) + (21871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224324421 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((11306081053 : ℚ) / 25000000000) : ℚ) : ℝ) + ((21871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21871:ℚ)^(-2:ℤ) : ℝ) = ((21871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2454 : ((((226121623149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21871 < q → q < 21881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21881).mp (by decide +kernel))) hgap
  have hprev := s2L_2453
  have hrat : ((226121623149 : ℚ) / 500000000000) ≤ ((45224324421 : ℚ) / 100000000000) + (21881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121623149 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224324421 : ℚ) / 100000000000) : ℚ) : ℝ) + ((21881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21881:ℚ)^(-2:ℤ) : ℝ) = ((21881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2455 : ((((1766575189 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21881 < q → q < 21893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21893).mp (by decide +kernel))) hgap
  have hprev := s2L_2454
  have hrat : ((1766575189 : ℚ) / 3906250000) ≤ ((226121623149 : ℚ) / 500000000000) + (21893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1766575189 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((226121623149 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21893:ℚ)^(-2:ℤ) : ℝ) = ((21893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2456 : ((((226121625233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21893 < q → q < 21911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21911).mp (by decide +kernel))) hgap
  have hprev := s2L_2455
  have hrat : ((226121625233 : ℚ) / 500000000000) ≤ ((1766575189 : ℚ) / 3906250000) + (21911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121625233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1766575189 : ℚ) / 3906250000) : ℚ) : ℝ) + ((21911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21911:ℚ)^(-2:ℤ) : ℝ) = ((21911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2457 : ((((90448650509 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21911 < q → q < 21929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21929).mp (by decide +kernel))) hgap
  have hprev := s2L_2456
  have hrat : ((90448650509 : ℚ) / 200000000000) ≤ ((226121625233 : ℚ) / 500000000000) + (21929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448650509 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121625233 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21929:ℚ)^(-2:ℤ) : ℝ) = ((21929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2458 : ((((226121627311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21929 < q → q < 21937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21937).mp (by decide +kernel))) hgap
  have hprev := s2L_2457
  have hrat : ((226121627311 : ℚ) / 500000000000) ≤ ((90448650509 : ℚ) / 200000000000) + (21937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121627311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448650509 : ℚ) / 200000000000) : ℚ) : ℝ) + ((21937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21937:ℚ)^(-2:ℤ) : ℝ) = ((21937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2459 : ((((226121628349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21943, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21937 < q → q < 21943 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21943).mp (by decide +kernel))) hgap
  have hprev := s2L_2458
  have hrat : ((226121628349 : ℚ) / 500000000000) ≤ ((226121627311 : ℚ) / 500000000000) + (21943:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121628349 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121627311 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21943:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21943:ℚ)^(-2:ℤ) : ℝ) = ((21943:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2460 : ((((452243258771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21943 < q → q < 21961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21961).mp (by decide +kernel))) hgap
  have hprev := s2L_2459
  have hrat : ((452243258771 : ℚ) / 1000000000000) ≤ ((226121628349 : ℚ) / 500000000000) + (21961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243258771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121628349 : ℚ) / 500000000000) : ℚ) : ℝ) + ((21961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21961:ℚ)^(-2:ℤ) : ℝ) = ((21961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2461 : ((((452243260841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21961 < q → q < 21977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21977).mp (by decide +kernel))) hgap
  have hprev := s2L_2460
  have hrat : ((452243260841 : ℚ) / 1000000000000) ≤ ((452243258771 : ℚ) / 1000000000000) + (21977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243260841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243258771 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21977:ℚ)^(-2:ℤ) : ℝ) = ((21977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2462 : ((((113060815727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21991, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21977 < q → q < 21991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21991).mp (by decide +kernel))) hgap
  have hprev := s2L_2461
  have hrat : ((113060815727 : ℚ) / 250000000000) ≤ ((452243260841 : ℚ) / 1000000000000) + (21991:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060815727 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243260841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((21991:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21991:ℚ)^(-2:ℤ) : ℝ) = ((21991:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2463 : ((((226121632487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 21997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21991 < q → q < 21997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 21997).mp (by decide +kernel))) hgap
  have hprev := s2L_2462
  have hrat : ((226121632487 : ℚ) / 500000000000) ≤ ((113060815727 : ℚ) / 250000000000) + (21997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121632487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060815727 : ℚ) / 250000000000) : ℚ) : ℝ) + ((21997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((21997:ℚ)^(-2:ℤ) : ℝ) = ((21997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2464 : ((((452243267039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 21997 < q → q < 22003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22003).mp (by decide +kernel))) hgap
  have hprev := s2L_2463
  have hrat : ((452243267039 : ℚ) / 1000000000000) ≤ ((226121632487 : ℚ) / 500000000000) + (22003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243267039 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121632487 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22003:ℚ)^(-2:ℤ) : ℝ) = ((22003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2465 : ((((226121634551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22003 < q → q < 22013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22013).mp (by decide +kernel))) hgap
  have hprev := s2L_2464
  have hrat : ((226121634551 : ℚ) / 500000000000) ≤ ((452243267039 : ℚ) / 1000000000000) + (22013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121634551 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243267039 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22013:ℚ)^(-2:ℤ) : ℝ) = ((22013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2466 : ((((452243271163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22013 < q → q < 22027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22027).mp (by decide +kernel))) hgap
  have hprev := s2L_2465
  have hrat : ((452243271163 : ℚ) / 1000000000000) ≤ ((226121634551 : ℚ) / 500000000000) + (22027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243271163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121634551 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22027:ℚ)^(-2:ℤ) : ℝ) = ((22027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2467 : ((((452243273223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22031, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22027 < q → q < 22031 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22031).mp (by decide +kernel))) hgap
  have hprev := s2L_2466
  have hrat : ((452243273223 : ℚ) / 1000000000000) ≤ ((452243271163 : ℚ) / 1000000000000) + (22031:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243273223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243271163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22031:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22031:ℚ)^(-2:ℤ) : ℝ) = ((22031:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2468 : ((((226121637641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22031 < q → q < 22037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22037).mp (by decide +kernel))) hgap
  have hprev := s2L_2467
  have hrat : ((226121637641 : ℚ) / 500000000000) ≤ ((452243273223 : ℚ) / 1000000000000) + (22037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121637641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243273223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22037:ℚ)^(-2:ℤ) : ℝ) = ((22037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2469 : ((((22612163867 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22037 < q → q < 22039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22039).mp (by decide +kernel))) hgap
  have hprev := s2L_2468
  have hrat : ((22612163867 : ℚ) / 50000000000) ≤ ((226121637641 : ℚ) / 500000000000) + (22039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612163867 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226121637641 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22039:ℚ)^(-2:ℤ) : ℝ) = ((22039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2470 : ((((113060819849 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22051, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22039 < q → q < 22051 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22051).mp (by decide +kernel))) hgap
  have hprev := s2L_2469
  have hrat : ((113060819849 : ℚ) / 250000000000) ≤ ((22612163867 : ℚ) / 50000000000) + (22051:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060819849 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22612163867 : ℚ) / 50000000000) : ℚ) : ℝ) + ((22051:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22051:ℚ)^(-2:ℤ) : ℝ) = ((22051:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2471 : ((((9044865629 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22051 < q → q < 22063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22063).mp (by decide +kernel))) hgap
  have hprev := s2L_2470
  have hrat : ((9044865629 : ℚ) / 20000000000) ≤ ((113060819849 : ℚ) / 250000000000) + (22063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044865629 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((113060819849 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22063:ℚ)^(-2:ℤ) : ℝ) = ((22063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2472 : ((((452243283503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22063 < q → q < 22067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22067).mp (by decide +kernel))) hgap
  have hprev := s2L_2471
  have hrat : ((452243283503 : ℚ) / 1000000000000) ≤ ((9044865629 : ℚ) / 20000000000) + (22067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243283503 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044865629 : ℚ) / 20000000000) : ℚ) : ℝ) + ((22067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22067:ℚ)^(-2:ℤ) : ℝ) = ((22067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2473 : ((((90448657111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22067 < q → q < 22073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22073).mp (by decide +kernel))) hgap
  have hprev := s2L_2472
  have hrat : ((90448657111 : ℚ) / 200000000000) ≤ ((452243283503 : ℚ) / 1000000000000) + (22073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448657111 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452243283503 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22073:ℚ)^(-2:ℤ) : ℝ) = ((22073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2474 : ((((226121643803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22073 < q → q < 22079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22079).mp (by decide +kernel))) hgap
  have hprev := s2L_2473
  have hrat : ((226121643803 : ℚ) / 500000000000) ≤ ((90448657111 : ℚ) / 200000000000) + (22079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121643803 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448657111 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22079:ℚ)^(-2:ℤ) : ℝ) = ((22079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2475 : ((((90448657931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22079 < q → q < 22091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22091).mp (by decide +kernel))) hgap
  have hprev := s2L_2474
  have hrat : ((90448657931 : ℚ) / 200000000000) ≤ ((226121643803 : ℚ) / 500000000000) + (22091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448657931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121643803 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22091:ℚ)^(-2:ℤ) : ℝ) = ((22091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2476 : ((((452243291703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22091 < q → q < 22093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22093).mp (by decide +kernel))) hgap
  have hprev := s2L_2475
  have hrat : ((452243291703 : ℚ) / 1000000000000) ≤ ((90448657931 : ℚ) / 200000000000) + (22093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243291703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448657931 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22093:ℚ)^(-2:ℤ) : ℝ) = ((22093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2477 : ((((113060823437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22093 < q → q < 22109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22109).mp (by decide +kernel))) hgap
  have hprev := s2L_2476
  have hrat : ((113060823437 : ℚ) / 250000000000) ≤ ((452243291703 : ℚ) / 1000000000000) + (22109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060823437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243291703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22109:ℚ)^(-2:ℤ) : ℝ) = ((22109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2478 : ((((452243295793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22109 < q → q < 22111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22111).mp (by decide +kernel))) hgap
  have hprev := s2L_2477
  have hrat : ((452243295793 : ℚ) / 1000000000000) ≤ ((113060823437 : ℚ) / 250000000000) + (22111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243295793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060823437 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22111:ℚ)^(-2:ℤ) : ℝ) = ((22111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2479 : ((((113060824459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22111 < q → q < 22123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22123).mp (by decide +kernel))) hgap
  have hprev := s2L_2478
  have hrat : ((113060824459 : ℚ) / 250000000000) ≤ ((452243295793 : ℚ) / 1000000000000) + (22123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060824459 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243295793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22123:ℚ)^(-2:ℤ) : ℝ) = ((22123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2480 : ((((226121649939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22123 < q → q < 22129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22129).mp (by decide +kernel))) hgap
  have hprev := s2L_2479
  have hrat : ((226121649939 : ℚ) / 500000000000) ≤ ((113060824459 : ℚ) / 250000000000) + (22129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121649939 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060824459 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22129:ℚ)^(-2:ℤ) : ℝ) = ((22129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2481 : ((((452243301919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22129 < q → q < 22133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22133).mp (by decide +kernel))) hgap
  have hprev := s2L_2480
  have hrat : ((452243301919 : ℚ) / 1000000000000) ≤ ((226121649939 : ℚ) / 500000000000) + (22133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243301919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121649939 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22133:ℚ)^(-2:ℤ) : ℝ) = ((22133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2482 : ((((452243303957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22133 < q → q < 22147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22147).mp (by decide +kernel))) hgap
  have hprev := s2L_2481
  have hrat : ((452243303957 : ℚ) / 1000000000000) ≤ ((452243301919 : ℚ) / 1000000000000) + (22147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243303957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243301919 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22147:ℚ)^(-2:ℤ) : ℝ) = ((22147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2483 : ((((226121652997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22153, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22147 < q → q < 22153 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22153).mp (by decide +kernel))) hgap
  have hprev := s2L_2482
  have hrat : ((226121652997 : ℚ) / 500000000000) ≤ ((452243303957 : ℚ) / 1000000000000) + (22153:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121652997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243303957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22153:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22153:ℚ)^(-2:ℤ) : ℝ) = ((22153:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2484 : ((((45224330803 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22153 < q → q < 22157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22157).mp (by decide +kernel))) hgap
  have hprev := s2L_2483
  have hrat : ((45224330803 : ℚ) / 100000000000) ≤ ((226121652997 : ℚ) / 500000000000) + (22157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224330803 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226121652997 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22157:ℚ)^(-2:ℤ) : ℝ) = ((22157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2485 : ((((226121655033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22157 < q → q < 22159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22159).mp (by decide +kernel))) hgap
  have hprev := s2L_2484
  have hrat : ((226121655033 : ℚ) / 500000000000) ≤ ((45224330803 : ℚ) / 100000000000) + (22159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121655033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224330803 : ℚ) / 100000000000) : ℚ) : ℝ) + ((22159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22159:ℚ)^(-2:ℤ) : ℝ) = ((22159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2486 : ((((4522433121 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22159 < q → q < 22171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22171).mp (by decide +kernel))) hgap
  have hprev := s2L_2485
  have hrat : ((4522433121 : ℚ) / 10000000000) ≤ ((226121655033 : ℚ) / 500000000000) + (22171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522433121 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226121655033 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22171:ℚ)^(-2:ℤ) : ℝ) = ((22171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2487 : ((((452243314131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22189, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22171 < q → q < 22189 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22189).mp (by decide +kernel))) hgap
  have hprev := s2L_2486
  have hrat : ((452243314131 : ℚ) / 1000000000000) ≤ ((4522433121 : ℚ) / 10000000000) + (22189:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243314131 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522433121 : ℚ) / 10000000000) : ℚ) : ℝ) + ((22189:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22189:ℚ)^(-2:ℤ) : ℝ) = ((22189:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2488 : ((((452243316161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22189 < q → q < 22193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22193).mp (by decide +kernel))) hgap
  have hprev := s2L_2487
  have hrat : ((452243316161 : ℚ) / 1000000000000) ≤ ((452243314131 : ℚ) / 1000000000000) + (22193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243316161 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243314131 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22193:ℚ)^(-2:ℤ) : ℝ) = ((22193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2489 : ((((56530414773 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22193 < q → q < 22229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22229).mp (by decide +kernel))) hgap
  have hprev := s2L_2488
  have hrat : ((56530414773 : ℚ) / 125000000000) ≤ ((452243316161 : ℚ) / 1000000000000) + (22229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530414773 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452243316161 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22229:ℚ)^(-2:ℤ) : ℝ) = ((22229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2490 : ((((113060830051 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22229 < q → q < 22247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22247).mp (by decide +kernel))) hgap
  have hprev := s2L_2489
  have hrat : ((113060830051 : ℚ) / 250000000000) ≤ ((56530414773 : ℚ) / 125000000000) + (22247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060830051 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56530414773 : ℚ) / 125000000000) : ℚ) : ℝ) + ((22247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22247:ℚ)^(-2:ℤ) : ℝ) = ((22247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2491 : ((((226121661111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22247 < q → q < 22259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22259).mp (by decide +kernel))) hgap
  have hprev := s2L_2490
  have hrat : ((226121661111 : ℚ) / 500000000000) ≤ ((113060830051 : ℚ) / 250000000000) + (22259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121661111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060830051 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22259:ℚ)^(-2:ℤ) : ℝ) = ((22259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2492 : ((((226121662119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22259 < q → q < 22271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22271).mp (by decide +kernel))) hgap
  have hprev := s2L_2491
  have hrat : ((226121662119 : ℚ) / 500000000000) ≤ ((226121661111 : ℚ) / 500000000000) + (22271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121662119 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226121661111 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22271:ℚ)^(-2:ℤ) : ℝ) = ((22271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2493 : ((((452243326253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22271 < q → q < 22273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22273).mp (by decide +kernel))) hgap
  have hprev := s2L_2492
  have hrat : ((452243326253 : ℚ) / 1000000000000) ≤ ((226121662119 : ℚ) / 500000000000) + (22273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243326253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121662119 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22273:ℚ)^(-2:ℤ) : ℝ) = ((22273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2494 : ((((113060832067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22273 < q → q < 22277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22277).mp (by decide +kernel))) hgap
  have hprev := s2L_2493
  have hrat : ((113060832067 : ℚ) / 250000000000) ≤ ((452243326253 : ℚ) / 1000000000000) + (22277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060832067 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452243326253 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22277:ℚ)^(-2:ℤ) : ℝ) = ((22277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2495 : ((((226121665141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22277 < q → q < 22279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22279).mp (by decide +kernel))) hgap
  have hprev := s2L_2494
  have hrat : ((226121665141 : ℚ) / 500000000000) ≤ ((113060832067 : ℚ) / 250000000000) + (22279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121665141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060832067 : ℚ) / 250000000000) : ℚ) : ℝ) + ((22279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22279:ℚ)^(-2:ℤ) : ℝ) = ((22279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2496 : ((((90448666459 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22279 < q → q < 22283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22283).mp (by decide +kernel))) hgap
  have hprev := s2L_2495
  have hrat : ((90448666459 : ℚ) / 200000000000) ≤ ((226121665141 : ℚ) / 500000000000) + (22283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448666459 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226121665141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22283:ℚ)^(-2:ℤ) : ℝ) = ((22283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2497 : ((((452243334307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22283 < q → q < 22291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22291).mp (by decide +kernel))) hgap
  have hprev := s2L_2496
  have hrat : ((452243334307 : ℚ) / 1000000000000) ≤ ((90448666459 : ℚ) / 200000000000) + (22291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243334307 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448666459 : ℚ) / 200000000000) : ℚ) : ℝ) + ((22291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22291:ℚ)^(-2:ℤ) : ℝ) = ((22291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2498 : ((((452243336317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22291 < q → q < 22303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22303).mp (by decide +kernel))) hgap
  have hprev := s2L_2497
  have hrat : ((452243336317 : ℚ) / 1000000000000) ≤ ((452243334307 : ℚ) / 1000000000000) + (22303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243336317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243334307 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22303:ℚ)^(-2:ℤ) : ℝ) = ((22303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2499 : ((((226121669163 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22303 < q → q < 22307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22307).mp (by decide +kernel))) hgap
  have hprev := s2L_2498
  have hrat : ((226121669163 : ℚ) / 500000000000) ≤ ((452243336317 : ℚ) / 1000000000000) + (22307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226121669163 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452243336317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22307:ℚ)^(-2:ℤ) : ℝ) = ((22307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2500 : ((((452243340329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22307 < q → q < 22343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22343).mp (by decide +kernel))) hgap
  have hprev := s2L_2499
  have hrat : ((452243340329 : ℚ) / 1000000000000) ≤ ((226121669163 : ℚ) / 500000000000) + (22343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243340329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226121669163 : ℚ) / 500000000000) : ℚ) : ℝ) + ((22343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22343:ℚ)^(-2:ℤ) : ℝ) = ((22343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_2501 : ((((452243342331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 22349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 22343 < q → q < 22349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 22349).mp (by decide +kernel))) hgap
  have hprev := s2L_2500
  have hrat : ((452243342331 : ℚ) / 1000000000000) ≤ ((452243340329 : ℚ) / 1000000000000) + (22349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452243342331 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452243340329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((22349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((22349:ℚ)^(-2:ℤ) : ℝ) = ((22349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))

end

end Work.RHContract.RegionI
