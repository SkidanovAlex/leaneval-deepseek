import Mathlib
import Submission.Work.RHContract.A.RegionI.Data08

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

lemma s2L_702 : ((((11305690449 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5297 < q → q < 5303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5303).mp (by decide +kernel))) hgap
  have hprev := s2L_701
  have hrat : ((11305690449 : ℚ) / 25000000000) ≤ ((452227582401 : ℚ) / 1000000000000) + (5303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305690449 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452227582401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5303:ℚ)^(-2:ℤ) : ℝ) = ((5303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_703 : ((((452227653439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5303 < q → q < 5309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5309).mp (by decide +kernel))) hgap
  have hprev := s2L_702
  have hrat : ((452227653439 : ℚ) / 1000000000000) ≤ ((11305690449 : ℚ) / 25000000000) + (5309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227653439 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11305690449 : ℚ) / 25000000000) : ℚ) : ℝ) + ((5309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5309:ℚ)^(-2:ℤ) : ℝ) = ((5309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_704 : ((((452227688731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5309 < q → q < 5323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5323).mp (by decide +kernel))) hgap
  have hprev := s2L_703
  have hrat : ((452227688731 : ℚ) / 1000000000000) ≤ ((452227653439 : ℚ) / 1000000000000) + (5323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227688731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227653439 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5323:ℚ)^(-2:ℤ) : ℝ) = ((5323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_705 : ((((452227723891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5323 < q → q < 5333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5333).mp (by decide +kernel))) hgap
  have hprev := s2L_704
  have hrat : ((452227723891 : ℚ) / 1000000000000) ≤ ((452227688731 : ℚ) / 1000000000000) + (5333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227723891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227688731 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5333:ℚ)^(-2:ℤ) : ℝ) = ((5333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_706 : ((((452227758867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5333 < q → q < 5347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5347).mp (by decide +kernel))) hgap
  have hprev := s2L_705
  have hrat : ((452227758867 : ℚ) / 1000000000000) ≤ ((452227723891 : ℚ) / 1000000000000) + (5347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227758867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227723891 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5347:ℚ)^(-2:ℤ) : ℝ) = ((5347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_707 : ((((452227793791 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5347 < q → q < 5351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5351).mp (by decide +kernel))) hgap
  have hprev := s2L_706
  have hrat : ((452227793791 : ℚ) / 1000000000000) ≤ ((452227758867 : ℚ) / 1000000000000) + (5351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227793791 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227758867 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5351:ℚ)^(-2:ℤ) : ℝ) = ((5351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_708 : ((((452227828327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5351 < q → q < 5381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5381).mp (by decide +kernel))) hgap
  have hprev := s2L_707
  have hrat : ((452227828327 : ℚ) / 1000000000000) ≤ ((452227793791 : ℚ) / 1000000000000) + (5381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227828327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452227793791 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5381:ℚ)^(-2:ℤ) : ℝ) = ((5381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_709 : ((((226113931393 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5381 < q → q < 5387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5387).mp (by decide +kernel))) hgap
  have hprev := s2L_708
  have hrat : ((226113931393 : ℚ) / 500000000000) ≤ ((452227828327 : ℚ) / 1000000000000) + (5387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113931393 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452227828327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5387:ℚ)^(-2:ℤ) : ℝ) = ((5387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_710 : ((((28264243573 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5387 < q → q < 5393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5393).mp (by decide +kernel))) hgap
  have hprev := s2L_709
  have hrat : ((28264243573 : ℚ) / 62500000000) ≤ ((226113931393 : ℚ) / 500000000000) + (5393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264243573 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226113931393 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5393:ℚ)^(-2:ℤ) : ℝ) = ((5393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_711 : ((((226113965737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5393 < q → q < 5399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5399).mp (by decide +kernel))) hgap
  have hprev := s2L_710
  have hrat : ((226113965737 : ℚ) / 500000000000) ≤ ((28264243573 : ℚ) / 62500000000) + (5399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113965737 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264243573 : ℚ) / 62500000000) : ℚ) : ℝ) + ((5399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5399:ℚ)^(-2:ℤ) : ℝ) = ((5399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_712 : ((((226113982839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5407, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5399 < q → q < 5407 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5407).mp (by decide +kernel))) hgap
  have hprev := s2L_711
  have hrat : ((226113982839 : ℚ) / 500000000000) ≤ ((226113965737 : ℚ) / 500000000000) + (5407:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226113982839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226113965737 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5407:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5407:ℚ)^(-2:ℤ) : ℝ) = ((5407:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_713 : ((((452227999807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5407 < q → q < 5413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5413).mp (by decide +kernel))) hgap
  have hprev := s2L_712
  have hrat : ((452227999807 : ℚ) / 1000000000000) ≤ ((226113982839 : ℚ) / 500000000000) + (5413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452227999807 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226113982839 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5413:ℚ)^(-2:ℤ) : ℝ) = ((5413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_714 : ((((90445606777 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5413 < q → q < 5417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5417).mp (by decide +kernel))) hgap
  have hprev := s2L_713
  have hrat : ((90445606777 : ℚ) / 200000000000) ≤ ((452227999807 : ℚ) / 1000000000000) + (5417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445606777 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452227999807 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5417:ℚ)^(-2:ℤ) : ℝ) = ((5417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_715 : ((((226114033969 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5417 < q → q < 5419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5419).mp (by decide +kernel))) hgap
  have hprev := s2L_714
  have hrat : ((226114033969 : ℚ) / 500000000000) ≤ ((90445606777 : ℚ) / 200000000000) + (5419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114033969 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90445606777 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5419:ℚ)^(-2:ℤ) : ℝ) = ((5419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_716 : ((((452228101841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5419 < q → q < 5431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5431).mp (by decide +kernel))) hgap
  have hprev := s2L_715
  have hrat : ((452228101841 : ℚ) / 1000000000000) ≤ ((226114033969 : ℚ) / 500000000000) + (5431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228101841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226114033969 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5431:ℚ)^(-2:ℤ) : ℝ) = ((5431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_717 : ((((452228135669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5431 < q → q < 5437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5437).mp (by decide +kernel))) hgap
  have hprev := s2L_716
  have hrat : ((452228135669 : ℚ) / 1000000000000) ≤ ((452228101841 : ℚ) / 1000000000000) + (5437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228135669 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452228101841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5437:ℚ)^(-2:ℤ) : ℝ) = ((5437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_718 : ((((452228169447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5437 < q → q < 5441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5441).mp (by decide +kernel))) hgap
  have hprev := s2L_717
  have hrat : ((452228169447 : ℚ) / 1000000000000) ≤ ((452228135669 : ℚ) / 1000000000000) + (5441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228169447 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452228135669 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5441:ℚ)^(-2:ℤ) : ℝ) = ((5441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_719 : ((((282642627 : ℚ) / 625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5441 < q → q < 5443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5443).mp (by decide +kernel))) hgap
  have hprev := s2L_718
  have hrat : ((282642627 : ℚ) / 625000000) ≤ ((452228169447 : ℚ) / 1000000000000) + (5443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((282642627 : ℚ) / 625000000) : ℚ) : ℝ) ≤ ((((452228169447 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5443:ℚ)^(-2:ℤ) : ℝ) = ((5443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_720 : ((((452228236879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5443 < q → q < 5449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5449).mp (by decide +kernel))) hgap
  have hprev := s2L_719
  have hrat : ((452228236879 : ℚ) / 1000000000000) ≤ ((282642627 : ℚ) / 625000000) + (5449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228236879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((282642627 : ℚ) / 625000000) : ℚ) : ℝ) + ((5449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5449:ℚ)^(-2:ℤ) : ℝ) = ((5449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_721 : ((((28264266893 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5449 < q → q < 5471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5471).mp (by decide +kernel))) hgap
  have hprev := s2L_720
  have hrat : ((28264266893 : ℚ) / 62500000000) ≤ ((452228236879 : ℚ) / 1000000000000) + (5471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264266893 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452228236879 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5471:ℚ)^(-2:ℤ) : ℝ) = ((5471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_722 : ((((56528537953 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5471 < q → q < 5477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5477).mp (by decide +kernel))) hgap
  have hprev := s2L_721
  have hrat : ((56528537953 : ℚ) / 125000000000) ≤ ((28264266893 : ℚ) / 62500000000) + (5477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528537953 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28264266893 : ℚ) / 62500000000) : ℚ) : ℝ) + ((5477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5477:ℚ)^(-2:ℤ) : ℝ) = ((5477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_723 : ((((90445667387 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5477 < q → q < 5479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5479).mp (by decide +kernel))) hgap
  have hprev := s2L_722
  have hrat : ((90445667387 : ℚ) / 200000000000) ≤ ((56528537953 : ℚ) / 125000000000) + (5479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445667387 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56528537953 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5479:ℚ)^(-2:ℤ) : ℝ) = ((5479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_724 : ((((226114185099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5479 < q → q < 5483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5483).mp (by decide +kernel))) hgap
  have hprev := s2L_723
  have hrat : ((226114185099 : ℚ) / 500000000000) ≤ ((90445667387 : ℚ) / 200000000000) + (5483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114185099 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90445667387 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5483:ℚ)^(-2:ℤ) : ℝ) = ((5483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_725 : ((((452228403243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5483 < q → q < 5501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5501).mp (by decide +kernel))) hgap
  have hprev := s2L_724
  have hrat : ((452228403243 : ℚ) / 1000000000000) ≤ ((226114185099 : ℚ) / 500000000000) + (5501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228403243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226114185099 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5501:ℚ)^(-2:ℤ) : ℝ) = ((5501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_726 : ((((56528554533 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5501 < q → q < 5503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5503).mp (by decide +kernel))) hgap
  have hprev := s2L_725
  have hrat : ((56528554533 : ℚ) / 125000000000) ≤ ((452228403243 : ℚ) / 1000000000000) + (5503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528554533 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452228403243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5503:ℚ)^(-2:ℤ) : ℝ) = ((5503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_727 : ((((452228469237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5507, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5503 < q → q < 5507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5507).mp (by decide +kernel))) hgap
  have hprev := s2L_726
  have hrat : ((452228469237 : ℚ) / 1000000000000) ≤ ((56528554533 : ℚ) / 125000000000) + (5507:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228469237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528554533 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5507:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5507:ℚ)^(-2:ℤ) : ℝ) = ((5507:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_728 : ((((452228502067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5507 < q → q < 5519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5519).mp (by decide +kernel))) hgap
  have hprev := s2L_727
  have hrat : ((452228502067 : ℚ) / 1000000000000) ≤ ((452228469237 : ℚ) / 1000000000000) + (5519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228502067 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452228469237 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5519:ℚ)^(-2:ℤ) : ℝ) = ((5519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_729 : ((((452228534873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5519 < q → q < 5521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5521).mp (by decide +kernel))) hgap
  have hprev := s2L_728
  have hrat : ((452228534873 : ℚ) / 1000000000000) ≤ ((452228502067 : ℚ) / 1000000000000) + (5521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228534873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452228502067 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5521:ℚ)^(-2:ℤ) : ℝ) = ((5521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_730 : ((((56528570951 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5521 < q → q < 5527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5527).mp (by decide +kernel))) hgap
  have hprev := s2L_729
  have hrat : ((56528570951 : ℚ) / 125000000000) ≤ ((452228534873 : ℚ) / 1000000000000) + (5527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528570951 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452228534873 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5527:ℚ)^(-2:ℤ) : ℝ) = ((5527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_731 : ((((56528575037 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5527 < q → q < 5531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5531).mp (by decide +kernel))) hgap
  have hprev := s2L_730
  have hrat : ((56528575037 : ℚ) / 125000000000) ≤ ((56528570951 : ℚ) / 125000000000) + (5531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528575037 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((56528570951 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5531:ℚ)^(-2:ℤ) : ℝ) = ((5531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_732 : ((((452228632679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5557, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5531 < q → q < 5557 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5557).mp (by decide +kernel))) hgap
  have hprev := s2L_731
  have hrat : ((452228632679 : ℚ) / 1000000000000) ≤ ((56528575037 : ℚ) / 125000000000) + (5557:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228632679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528575037 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5557:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5557:ℚ)^(-2:ℤ) : ℝ) = ((5557:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_733 : ((((14132145781 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5557 < q → q < 5563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5563).mp (by decide +kernel))) hgap
  have hprev := s2L_732
  have hrat : ((14132145781 : ℚ) / 31250000000) ≤ ((452228632679 : ℚ) / 1000000000000) + (5563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132145781 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452228632679 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5563:ℚ)^(-2:ℤ) : ℝ) = ((5563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_734 : ((((90445739447 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5563 < q → q < 5569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5569).mp (by decide +kernel))) hgap
  have hprev := s2L_733
  have hrat : ((90445739447 : ℚ) / 200000000000) ≤ ((14132145781 : ℚ) / 31250000000) + (5569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445739447 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14132145781 : ℚ) / 31250000000) : ℚ) : ℝ) + ((5569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5569:ℚ)^(-2:ℤ) : ℝ) = ((5569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_735 : ((((56528591179 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5569 < q → q < 5573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5573).mp (by decide +kernel))) hgap
  have hprev := s2L_734
  have hrat : ((56528591179 : ℚ) / 125000000000) ≤ ((90445739447 : ℚ) / 200000000000) + (5573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528591179 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90445739447 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5573:ℚ)^(-2:ℤ) : ℝ) = ((5573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_736 : ((((452228761537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5573 < q → q < 5581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5581).mp (by decide +kernel))) hgap
  have hprev := s2L_735
  have hrat : ((452228761537 : ℚ) / 1000000000000) ≤ ((56528591179 : ℚ) / 125000000000) + (5581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228761537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528591179 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5581:ℚ)^(-2:ℤ) : ℝ) = ((5581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_737 : ((((452228793527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5581 < q → q < 5591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5591).mp (by decide +kernel))) hgap
  have hprev := s2L_736
  have hrat : ((452228793527 : ℚ) / 1000000000000) ≤ ((452228761537 : ℚ) / 1000000000000) + (5591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228793527 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452228761537 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5591:ℚ)^(-2:ℤ) : ℝ) = ((5591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_738 : ((((226114412577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5591 < q → q < 5623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5623).mp (by decide +kernel))) hgap
  have hprev := s2L_737
  have hrat : ((226114412577 : ℚ) / 500000000000) ≤ ((452228793527 : ℚ) / 1000000000000) + (5623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114412577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452228793527 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5623:ℚ)^(-2:ℤ) : ℝ) = ((5623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_739 : ((((226114428301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5623 < q → q < 5639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5639).mp (by decide +kernel))) hgap
  have hprev := s2L_738
  have hrat : ((226114428301 : ℚ) / 500000000000) ≤ ((226114412577 : ℚ) / 500000000000) + (5639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114428301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226114412577 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5639:ℚ)^(-2:ℤ) : ℝ) = ((5639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_740 : ((((452228888027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5639 < q → q < 5641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5641).mp (by decide +kernel))) hgap
  have hprev := s2L_739
  have hrat : ((452228888027 : ℚ) / 1000000000000) ≤ ((226114428301 : ℚ) / 500000000000) + (5641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452228888027 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226114428301 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5641:ℚ)^(-2:ℤ) : ℝ) = ((5641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_741 : ((((226114459693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5641 < q → q < 5647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5647).mp (by decide +kernel))) hgap
  have hprev := s2L_740
  have hrat : ((226114459693 : ℚ) / 500000000000) ≤ ((452228888027 : ℚ) / 1000000000000) + (5647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114459693 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452228888027 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5647:ℚ)^(-2:ℤ) : ℝ) = ((5647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_742 : ((((4522289507 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5651, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5647 < q → q < 5651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5651).mp (by decide +kernel))) hgap
  have hprev := s2L_741
  have hrat : ((4522289507 : ℚ) / 10000000000) ≤ ((226114459693 : ℚ) / 500000000000) + (5651:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522289507 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226114459693 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5651:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5651:ℚ)^(-2:ℤ) : ℝ) = ((5651:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_743 : ((((56528622749 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5651 < q → q < 5653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5653).mp (by decide +kernel))) hgap
  have hprev := s2L_742
  have hrat : ((56528622749 : ℚ) / 125000000000) ≤ ((4522289507 : ℚ) / 10000000000) + (5653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528622749 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((4522289507 : ℚ) / 10000000000) : ℚ) : ℝ) + ((5653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5653:ℚ)^(-2:ℤ) : ℝ) = ((5653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_744 : ((((11305725331 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5653 < q → q < 5657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5657).mp (by decide +kernel))) hgap
  have hprev := s2L_743
  have hrat : ((11305725331 : ℚ) / 25000000000) ≤ ((56528622749 : ℚ) / 125000000000) + (5657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305725331 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((56528622749 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5657:ℚ)^(-2:ℤ) : ℝ) = ((5657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_745 : ((((226114522233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5657 < q → q < 5659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5659).mp (by decide +kernel))) hgap
  have hprev := s2L_744
  have hrat : ((226114522233 : ℚ) / 500000000000) ≤ ((11305725331 : ℚ) / 25000000000) + (5659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114522233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11305725331 : ℚ) / 25000000000) : ℚ) : ℝ) + ((5659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5659:ℚ)^(-2:ℤ) : ℝ) = ((5659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_746 : ((((226114537791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5659 < q → q < 5669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5669).mp (by decide +kernel))) hgap
  have hprev := s2L_745
  have hrat : ((226114537791 : ℚ) / 500000000000) ≤ ((226114522233 : ℚ) / 500000000000) + (5669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114537791 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226114522233 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5669:ℚ)^(-2:ℤ) : ℝ) = ((5669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_747 : ((((90445821309 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5683, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5669 < q → q < 5683 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5683).mp (by decide +kernel))) hgap
  have hprev := s2L_746
  have hrat : ((90445821309 : ℚ) / 200000000000) ≤ ((226114537791 : ℚ) / 500000000000) + (5683:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445821309 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226114537791 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5683:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5683:ℚ)^(-2:ℤ) : ℝ) = ((5683:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_748 : ((((226114568721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5683 < q → q < 5689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5689).mp (by decide +kernel))) hgap
  have hprev := s2L_747
  have hrat : ((226114568721 : ℚ) / 500000000000) ≤ ((90445821309 : ℚ) / 200000000000) + (5689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114568721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90445821309 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5689:ℚ)^(-2:ℤ) : ℝ) = ((5689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_749 : ((((56528646037 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5689 < q → q < 5693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5693).mp (by decide +kernel))) hgap
  have hprev := s2L_748
  have hrat : ((56528646037 : ℚ) / 125000000000) ≤ ((226114568721 : ℚ) / 500000000000) + (5693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528646037 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226114568721 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5693:ℚ)^(-2:ℤ) : ℝ) = ((5693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_750 : ((((452229199063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5693 < q → q < 5701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5701).mp (by decide +kernel))) hgap
  have hprev := s2L_749
  have hrat : ((452229199063 : ℚ) / 1000000000000) ≤ ((56528646037 : ℚ) / 125000000000) + (5701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229199063 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528646037 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5701:ℚ)^(-2:ℤ) : ℝ) = ((5701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_751 : ((((452229229723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5701 < q → q < 5711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5711).mp (by decide +kernel))) hgap
  have hprev := s2L_750
  have hrat : ((452229229723 : ℚ) / 1000000000000) ≤ ((452229199063 : ℚ) / 1000000000000) + (5711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229229723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452229199063 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5711:ℚ)^(-2:ℤ) : ℝ) = ((5711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_752 : ((((226114630159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5711 < q → q < 5717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5717).mp (by decide +kernel))) hgap
  have hprev := s2L_751
  have hrat : ((226114630159 : ℚ) / 500000000000) ≤ ((452229229723 : ℚ) / 1000000000000) + (5717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114630159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452229229723 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5717:ℚ)^(-2:ℤ) : ℝ) = ((5717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_753 : ((((4522292907 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5717 < q → q < 5737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5737).mp (by decide +kernel))) hgap
  have hprev := s2L_752
  have hrat : ((4522292907 : ℚ) / 10000000000) ≤ ((226114630159 : ℚ) / 500000000000) + (5737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522292907 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226114630159 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5737:ℚ)^(-2:ℤ) : ℝ) = ((5737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_754 : ((((5652866513 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5737 < q → q < 5741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5741).mp (by decide +kernel))) hgap
  have hprev := s2L_753
  have hrat : ((5652866513 : ℚ) / 12500000000) ≤ ((4522292907 : ℚ) / 10000000000) + (5741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5652866513 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((4522292907 : ℚ) / 10000000000) : ℚ) : ℝ) + ((5741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5741:ℚ)^(-2:ℤ) : ℝ) = ((5741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_755 : ((((452229351359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5741 < q → q < 5743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5743).mp (by decide +kernel))) hgap
  have hprev := s2L_754
  have hrat : ((452229351359 : ℚ) / 1000000000000) ≤ ((5652866513 : ℚ) / 12500000000) + (5743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229351359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((5652866513 : ℚ) / 12500000000) : ℚ) : ℝ) + ((5743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5743:ℚ)^(-2:ℤ) : ℝ) = ((5743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_756 : ((((90445876323 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5743 < q → q < 5749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5749).mp (by decide +kernel))) hgap
  have hprev := s2L_755
  have hrat : ((90445876323 : ℚ) / 200000000000) ≤ ((452229351359 : ℚ) / 1000000000000) + (5749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445876323 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452229351359 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5749:ℚ)^(-2:ℤ) : ℝ) = ((5749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_757 : ((((452229411557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5749 < q → q < 5779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5779).mp (by decide +kernel))) hgap
  have hprev := s2L_756
  have hrat : ((452229411557 : ℚ) / 1000000000000) ≤ ((90445876323 : ℚ) / 200000000000) + (5779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229411557 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445876323 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5779:ℚ)^(-2:ℤ) : ℝ) = ((5779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_758 : ((((226114720729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5779 < q → q < 5783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5783).mp (by decide +kernel))) hgap
  have hprev := s2L_757
  have hrat : ((226114720729 : ℚ) / 500000000000) ≤ ((452229411557 : ℚ) / 1000000000000) + (5783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114720729 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452229411557 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5783:ℚ)^(-2:ℤ) : ℝ) = ((5783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_759 : ((((113057367819 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5783 < q → q < 5791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5791).mp (by decide +kernel))) hgap
  have hprev := s2L_758
  have hrat : ((113057367819 : ℚ) / 250000000000) ≤ ((226114720729 : ℚ) / 500000000000) + (5791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057367819 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226114720729 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5791:ℚ)^(-2:ℤ) : ℝ) = ((5791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_760 : ((((7066085953 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5791 < q → q < 5801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5801).mp (by decide +kernel))) hgap
  have hprev := s2L_759
  have hrat : ((7066085953 : ℚ) / 15625000000) ≤ ((113057367819 : ℚ) / 250000000000) + (5801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066085953 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((113057367819 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5801:ℚ)^(-2:ℤ) : ℝ) = ((5801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_761 : ((((226114765323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5801 < q → q < 5807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5807).mp (by decide +kernel))) hgap
  have hprev := s2L_760
  have hrat : ((226114765323 : ℚ) / 500000000000) ≤ ((7066085953 : ℚ) / 15625000000) + (5807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114765323 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((7066085953 : ℚ) / 15625000000) : ℚ) : ℝ) + ((5807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5807:ℚ)^(-2:ℤ) : ℝ) = ((5807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_762 : ((((452229560239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5807 < q → q < 5813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5813).mp (by decide +kernel))) hgap
  have hprev := s2L_761
  have hrat : ((452229560239 : ℚ) / 1000000000000) ≤ ((226114765323 : ℚ) / 500000000000) + (5813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229560239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226114765323 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5813:ℚ)^(-2:ℤ) : ℝ) = ((5813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_763 : ((((452229589751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5813 < q → q < 5821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5821).mp (by decide +kernel))) hgap
  have hprev := s2L_762
  have hrat : ((452229589751 : ℚ) / 1000000000000) ≤ ((452229560239 : ℚ) / 1000000000000) + (5821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229589751 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452229560239 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5821:ℚ)^(-2:ℤ) : ℝ) = ((5821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_764 : ((((226114809601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5821 < q → q < 5827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5827).mp (by decide +kernel))) hgap
  have hprev := s2L_763
  have hrat : ((226114809601 : ℚ) / 500000000000) ≤ ((452229589751 : ℚ) / 1000000000000) + (5827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114809601 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452229589751 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5827:ℚ)^(-2:ℤ) : ℝ) = ((5827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_765 : ((((113057412133 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5827 < q → q < 5839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5839).mp (by decide +kernel))) hgap
  have hprev := s2L_764
  have hrat : ((113057412133 : ℚ) / 250000000000) ≤ ((226114809601 : ℚ) / 500000000000) + (5839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057412133 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226114809601 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5839:ℚ)^(-2:ℤ) : ℝ) = ((5839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_766 : ((((226114838911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5843, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5839 < q → q < 5843 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5843).mp (by decide +kernel))) hgap
  have hprev := s2L_765
  have hrat : ((226114838911 : ℚ) / 500000000000) ≤ ((113057412133 : ℚ) / 250000000000) + (5843:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114838911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113057412133 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5843:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5843:ℚ)^(-2:ℤ) : ℝ) = ((5843:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_767 : ((((113057426763 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5849, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5843 < q → q < 5849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5849).mp (by decide +kernel))) hgap
  have hprev := s2L_766
  have hrat : ((113057426763 : ℚ) / 250000000000) ≤ ((226114838911 : ℚ) / 500000000000) + (5849:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057426763 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226114838911 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5849:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5849:ℚ)^(-2:ℤ) : ℝ) = ((5849:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_768 : ((((226114868131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5849 < q → q < 5851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5851).mp (by decide +kernel))) hgap
  have hprev := s2L_767
  have hrat : ((226114868131 : ℚ) / 500000000000) ≤ ((113057426763 : ℚ) / 250000000000) + (5851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114868131 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113057426763 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5851:ℚ)^(-2:ℤ) : ℝ) = ((5851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_769 : ((((113057441353 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5851 < q → q < 5857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5857).mp (by decide +kernel))) hgap
  have hprev := s2L_768
  have hrat : ((113057441353 : ℚ) / 250000000000) ≤ ((226114868131 : ℚ) / 500000000000) + (5857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057441353 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226114868131 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5857:ℚ)^(-2:ℤ) : ℝ) = ((5857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_770 : ((((226114897261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5857 < q → q < 5861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5861).mp (by decide +kernel))) hgap
  have hprev := s2L_769
  have hrat : ((226114897261 : ℚ) / 500000000000) ≤ ((113057441353 : ℚ) / 250000000000) + (5861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226114897261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113057441353 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5861:ℚ)^(-2:ℤ) : ℝ) = ((5861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_771 : ((((452229823573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5861 < q → q < 5867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5867).mp (by decide +kernel))) hgap
  have hprev := s2L_770
  have hrat : ((452229823573 : ℚ) / 1000000000000) ≤ ((226114897261 : ℚ) / 500000000000) + (5867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229823573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226114897261 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5867:ℚ)^(-2:ℤ) : ℝ) = ((5867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_772 : ((((113057463151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5869, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5867 < q → q < 5869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5869).mp (by decide +kernel))) hgap
  have hprev := s2L_771
  have hrat : ((113057463151 : ℚ) / 250000000000) ≤ ((452229823573 : ℚ) / 1000000000000) + (5869:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057463151 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452229823573 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5869:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5869:ℚ)^(-2:ℤ) : ℝ) = ((5869:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_773 : ((((7066091899 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5869 < q → q < 5879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5879).mp (by decide +kernel))) hgap
  have hprev := s2L_772
  have hrat : ((7066091899 : ℚ) / 15625000000) ≤ ((113057463151 : ℚ) / 250000000000) + (5879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066091899 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((113057463151 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5879:ℚ)^(-2:ℤ) : ℝ) = ((5879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_774 : ((((452229910449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5881, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5879 < q → q < 5881 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5881).mp (by decide +kernel))) hgap
  have hprev := s2L_773
  have hrat : ((452229910449 : ℚ) / 1000000000000) ≤ ((7066091899 : ℚ) / 15625000000) + (5881:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229910449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066091899 : ℚ) / 15625000000) : ℚ) : ℝ) + ((5881:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5881:ℚ)^(-2:ℤ) : ℝ) = ((5881:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_775 : ((((90445987841 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5897, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5881 < q → q < 5897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5897).mp (by decide +kernel))) hgap
  have hprev := s2L_774
  have hrat : ((90445987841 : ℚ) / 200000000000) ≤ ((452229910449 : ℚ) / 1000000000000) + (5897:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90445987841 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452229910449 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5897:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5897:ℚ)^(-2:ℤ) : ℝ) = ((5897:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_776 : ((((452229967903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5897 < q → q < 5903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5903).mp (by decide +kernel))) hgap
  have hprev := s2L_775
  have hrat : ((452229967903 : ℚ) / 1000000000000) ≤ ((90445987841 : ℚ) / 200000000000) + (5903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229967903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90445987841 : ℚ) / 200000000000) : ℚ) : ℝ) + ((5903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5903:ℚ)^(-2:ℤ) : ℝ) = ((5903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_777 : ((((452229996407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5903 < q → q < 5923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5923).mp (by decide +kernel))) hgap
  have hprev := s2L_776
  have hrat : ((452229996407 : ℚ) / 1000000000000) ≤ ((452229967903 : ℚ) / 1000000000000) + (5923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452229996407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452229967903 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5923:ℚ)^(-2:ℤ) : ℝ) = ((5923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_778 : ((((452230024873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5923 < q → q < 5927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5927).mp (by decide +kernel))) hgap
  have hprev := s2L_777
  have hrat : ((452230024873 : ℚ) / 1000000000000) ≤ ((452229996407 : ℚ) / 1000000000000) + (5927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230024873 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452229996407 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5927:ℚ)^(-2:ℤ) : ℝ) = ((5927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_779 : ((((56528756653 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5927 < q → q < 5939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5939).mp (by decide +kernel))) hgap
  have hprev := s2L_778
  have hrat : ((56528756653 : ℚ) / 125000000000) ≤ ((452230024873 : ℚ) / 1000000000000) + (5939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528756653 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452230024873 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((5939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5939:ℚ)^(-2:ℤ) : ℝ) = ((5939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_780 : ((((226115040721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5939 < q → q < 5953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5953).mp (by decide +kernel))) hgap
  have hprev := s2L_779
  have hrat : ((226115040721 : ℚ) / 500000000000) ≤ ((56528756653 : ℚ) / 125000000000) + (5953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115040721 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56528756653 : ℚ) / 125000000000) : ℚ) : ℝ) + ((5953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5953:ℚ)^(-2:ℤ) : ℝ) = ((5953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_781 : ((((113057527349 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5953 < q → q < 5981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5981).mp (by decide +kernel))) hgap
  have hprev := s2L_780
  have hrat : ((113057527349 : ℚ) / 250000000000) ≤ ((226115040721 : ℚ) / 500000000000) + (5981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057527349 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226115040721 : ℚ) / 500000000000) : ℚ) : ℝ) + ((5981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5981:ℚ)^(-2:ℤ) : ℝ) = ((5981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_782 : ((((226115068647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 5987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5981 < q → q < 5987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 5987).mp (by decide +kernel))) hgap
  have hprev := s2L_781
  have hrat : ((226115068647 : ℚ) / 500000000000) ≤ ((113057527349 : ℚ) / 250000000000) + (5987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115068647 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113057527349 : ℚ) / 250000000000) : ℚ) : ℝ) + ((5987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((5987:ℚ)^(-2:ℤ) : ℝ) = ((5987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_783 : ((((452230165007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 5987 < q → q < 6007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6007).mp (by decide +kernel))) hgap
  have hprev := s2L_782
  have hrat : ((452230165007 : ℚ) / 1000000000000) ≤ ((226115068647 : ℚ) / 500000000000) + (6007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230165007 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226115068647 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6007:ℚ)^(-2:ℤ) : ℝ) = ((6007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_784 : ((((452230192683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6007 < q → q < 6011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6011).mp (by decide +kernel))) hgap
  have hprev := s2L_783
  have hrat : ((452230192683 : ℚ) / 1000000000000) ≤ ((452230165007 : ℚ) / 1000000000000) + (6011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230192683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452230165007 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6011:ℚ)^(-2:ℤ) : ℝ) = ((6011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_785 : ((((226115110097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6011 < q → q < 6029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6029).mp (by decide +kernel))) hgap
  have hprev := s2L_784
  have hrat : ((226115110097 : ℚ) / 500000000000) ≤ ((452230192683 : ℚ) / 1000000000000) + (6029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115110097 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452230192683 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6029:ℚ)^(-2:ℤ) : ℝ) = ((6029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_786 : ((((28264390477 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6029 < q → q < 6037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6037).mp (by decide +kernel))) hgap
  have hprev := s2L_785
  have hrat : ((28264390477 : ℚ) / 62500000000) ≤ ((226115110097 : ℚ) / 500000000000) + (6037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264390477 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226115110097 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6037:ℚ)^(-2:ℤ) : ℝ) = ((6037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_787 : ((((90446055003 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6037 < q → q < 6043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6043).mp (by decide +kernel))) hgap
  have hprev := s2L_786
  have hrat : ((90446055003 : ℚ) / 200000000000) ≤ ((28264390477 : ℚ) / 62500000000) + (6043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446055003 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28264390477 : ℚ) / 62500000000) : ℚ) : ℝ) + ((6043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6043:ℚ)^(-2:ℤ) : ℝ) = ((6043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_788 : ((((226115151181 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6043 < q → q < 6047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6047).mp (by decide +kernel))) hgap
  have hprev := s2L_787
  have hrat : ((226115151181 : ℚ) / 500000000000) ≤ ((90446055003 : ℚ) / 200000000000) + (6047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115151181 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90446055003 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6047:ℚ)^(-2:ℤ) : ℝ) = ((6047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_789 : ((((90446065931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6047 < q → q < 6053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6053).mp (by decide +kernel))) hgap
  have hprev := s2L_788
  have hrat : ((90446065931 : ℚ) / 200000000000) ≤ ((226115151181 : ℚ) / 500000000000) + (6053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446065931 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226115151181 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6053:ℚ)^(-2:ℤ) : ℝ) = ((6053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_790 : ((((226115178411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6053 < q → q < 6067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6067).mp (by decide +kernel))) hgap
  have hprev := s2L_789
  have hrat : ((226115178411 : ℚ) / 500000000000) ≤ ((90446065931 : ℚ) / 200000000000) + (6067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115178411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90446065931 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6067:ℚ)^(-2:ℤ) : ℝ) = ((6067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_791 : ((((90446076787 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6067 < q → q < 6073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6073).mp (by decide +kernel))) hgap
  have hprev := s2L_790
  have hrat : ((90446076787 : ℚ) / 200000000000) ≤ ((226115178411 : ℚ) / 500000000000) + (6073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446076787 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226115178411 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6073:ℚ)^(-2:ℤ) : ℝ) = ((6073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_792 : ((((90446082199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6073 < q → q < 6079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6079).mp (by decide +kernel))) hgap
  have hprev := s2L_791
  have hrat : ((90446082199 : ℚ) / 200000000000) ≤ ((90446076787 : ℚ) / 200000000000) + (6079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446082199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90446076787 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6079:ℚ)^(-2:ℤ) : ℝ) = ((6079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_793 : ((((226115218983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6079 < q → q < 6089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6089).mp (by decide +kernel))) hgap
  have hprev := s2L_792
  have hrat : ((226115218983 : ℚ) / 500000000000) ≤ ((90446082199 : ℚ) / 200000000000) + (6089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115218983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90446082199 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6089:ℚ)^(-2:ℤ) : ℝ) = ((6089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_794 : ((((452230464919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6089 < q → q < 6091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6091).mp (by decide +kernel))) hgap
  have hprev := s2L_793
  have hrat : ((452230464919 : ℚ) / 1000000000000) ≤ ((226115218983 : ℚ) / 500000000000) + (6091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230464919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226115218983 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6091:ℚ)^(-2:ℤ) : ℝ) = ((6091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_795 : ((((56528811473 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6091 < q → q < 6101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6101).mp (by decide +kernel))) hgap
  have hprev := s2L_794
  have hrat : ((56528811473 : ℚ) / 125000000000) ≤ ((452230464919 : ℚ) / 1000000000000) + (6101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528811473 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452230464919 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6101:ℚ)^(-2:ℤ) : ℝ) = ((6101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_796 : ((((28264407409 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6101 < q → q < 6113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6113).mp (by decide +kernel))) hgap
  have hprev := s2L_795
  have hrat : ((28264407409 : ℚ) / 62500000000) ≤ ((56528811473 : ℚ) / 125000000000) + (6113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264407409 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56528811473 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6113:ℚ)^(-2:ℤ) : ℝ) = ((6113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_797 : ((((226115272617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6113 < q → q < 6121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6121).mp (by decide +kernel))) hgap
  have hprev := s2L_796
  have hrat : ((226115272617 : ℚ) / 500000000000) ≤ ((28264407409 : ℚ) / 62500000000) + (6121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115272617 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264407409 : ℚ) / 62500000000) : ℚ) : ℝ) + ((6121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6121:ℚ)^(-2:ℤ) : ℝ) = ((6121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_798 : ((((452230571837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6121 < q → q < 6131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6131).mp (by decide +kernel))) hgap
  have hprev := s2L_797
  have hrat : ((452230571837 : ℚ) / 1000000000000) ≤ ((226115272617 : ℚ) / 500000000000) + (6131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230571837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226115272617 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6131:ℚ)^(-2:ℤ) : ℝ) = ((6131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_799 : ((((452230598423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6131 < q → q < 6133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6133).mp (by decide +kernel))) hgap
  have hprev := s2L_798
  have hrat : ((452230598423 : ℚ) / 1000000000000) ≤ ((452230571837 : ℚ) / 1000000000000) + (6133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230598423 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452230571837 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6133:ℚ)^(-2:ℤ) : ℝ) = ((6133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_800 : ((((226115312461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6133 < q → q < 6143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6143).mp (by decide +kernel))) hgap
  have hprev := s2L_799
  have hrat : ((226115312461 : ℚ) / 500000000000) ≤ ((452230598423 : ℚ) / 1000000000000) + (6143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115312461 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452230598423 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6143:ℚ)^(-2:ℤ) : ℝ) = ((6143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_801 : ((((56528831419 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6143 < q → q < 6151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6151).mp (by decide +kernel))) hgap
  have hprev := s2L_800
  have hrat : ((56528831419 : ℚ) / 125000000000) ≤ ((226115312461 : ℚ) / 500000000000) + (6151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528831419 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226115312461 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6151:ℚ)^(-2:ℤ) : ℝ) = ((6151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_802 : ((((452230677679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6151 < q → q < 6163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6163).mp (by decide +kernel))) hgap
  have hprev := s2L_801
  have hrat : ((452230677679 : ℚ) / 1000000000000) ≤ ((56528831419 : ℚ) / 125000000000) + (6163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230677679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528831419 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6163:ℚ)^(-2:ℤ) : ℝ) = ((6163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_803 : ((((452230703921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6163 < q → q < 6173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6173).mp (by decide +kernel))) hgap
  have hprev := s2L_802
  have hrat : ((452230703921 : ℚ) / 1000000000000) ≤ ((452230677679 : ℚ) / 1000000000000) + (6173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230703921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452230677679 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6173:ℚ)^(-2:ℤ) : ℝ) = ((6173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_804 : ((((11305768249 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6173 < q → q < 6197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6197).mp (by decide +kernel))) hgap
  have hprev := s2L_803
  have hrat : ((11305768249 : ℚ) / 25000000000) ≤ ((452230703921 : ℚ) / 1000000000000) + (6197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305768249 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452230703921 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6197:ℚ)^(-2:ℤ) : ℝ) = ((6197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_805 : ((((226115377991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6199, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6197 < q → q < 6199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6199).mp (by decide +kernel))) hgap
  have hprev := s2L_804
  have hrat : ((226115377991 : ℚ) / 500000000000) ≤ ((11305768249 : ℚ) / 25000000000) + (6199:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115377991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11305768249 : ℚ) / 25000000000) : ℚ) : ℝ) + ((6199:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6199:ℚ)^(-2:ℤ) : ℝ) = ((6199:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_806 : ((((452230781971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6199 < q → q < 6203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6203).mp (by decide +kernel))) hgap
  have hprev := s2L_805
  have hrat : ((452230781971 : ℚ) / 1000000000000) ≤ ((226115377991 : ℚ) / 500000000000) + (6203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230781971 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226115377991 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6203:ℚ)^(-2:ℤ) : ℝ) = ((6203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_807 : ((((452230807893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6203 < q → q < 6211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6211).mp (by decide +kernel))) hgap
  have hprev := s2L_806
  have hrat : ((452230807893 : ℚ) / 1000000000000) ≤ ((452230781971 : ℚ) / 1000000000000) + (6211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230807893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452230781971 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6211:ℚ)^(-2:ℤ) : ℝ) = ((6211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_808 : ((((90446166753 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6211 < q → q < 6217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6217).mp (by decide +kernel))) hgap
  have hprev := s2L_807
  have hrat : ((90446166753 : ℚ) / 200000000000) ≤ ((452230807893 : ℚ) / 1000000000000) + (6217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446166753 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452230807893 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6217:ℚ)^(-2:ℤ) : ℝ) = ((6217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_809 : ((((113057714901 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6217 < q → q < 6221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6221).mp (by decide +kernel))) hgap
  have hprev := s2L_808
  have hrat : ((113057714901 : ℚ) / 250000000000) ≤ ((90446166753 : ℚ) / 200000000000) + (6221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057714901 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90446166753 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6221:ℚ)^(-2:ℤ) : ℝ) = ((6221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_810 : ((((110407931 : ℚ) / 244140625) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6221 < q → q < 6229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6229).mp (by decide +kernel))) hgap
  have hprev := s2L_809
  have hrat : ((110407931 : ℚ) / 244140625) ≤ ((113057714901 : ℚ) / 250000000000) + (6229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((110407931 : ℚ) / 244140625) : ℚ) : ℝ) ≤ ((((113057714901 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6229:ℚ)^(-2:ℤ) : ℝ) = ((6229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_811 : ((((452230911 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6229 < q → q < 6247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6247).mp (by decide +kernel))) hgap
  have hprev := s2L_810
  have hrat : ((452230911 : ℚ) / 1000000000) ≤ ((110407931 : ℚ) / 244140625) + (6247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452230911 : ℚ) / 1000000000) : ℚ) : ℝ) ≤ ((((110407931 : ℚ) / 244140625) : ℚ) : ℝ) + ((6247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6247:ℚ)^(-2:ℤ) : ℝ) = ((6247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_812 : ((((226115468271 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6247 < q → q < 6257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6257).mp (by decide +kernel))) hgap
  have hprev := s2L_811
  have hrat : ((226115468271 : ℚ) / 500000000000) ≤ ((452230911 : ℚ) / 1000000000) + (6257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115468271 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452230911 : ℚ) / 1000000000) : ℚ) : ℝ) + ((6257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6257:ℚ)^(-2:ℤ) : ℝ) = ((6257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_813 : ((((90446192407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6257 < q → q < 6263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6263).mp (by decide +kernel))) hgap
  have hprev := s2L_812
  have hrat : ((90446192407 : ℚ) / 200000000000) ≤ ((226115468271 : ℚ) / 500000000000) + (6263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446192407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226115468271 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6263:ℚ)^(-2:ℤ) : ℝ) = ((6263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_814 : ((((11305774687 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6263 < q → q < 6269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6269).mp (by decide +kernel))) hgap
  have hprev := s2L_813
  have hrat : ((11305774687 : ℚ) / 25000000000) ≤ ((90446192407 : ℚ) / 200000000000) + (6269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305774687 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((90446192407 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6269:ℚ)^(-2:ℤ) : ℝ) = ((6269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_815 : ((((113057753227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6269 < q → q < 6271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6271).mp (by decide +kernel))) hgap
  have hprev := s2L_814
  have hrat : ((113057753227 : ℚ) / 250000000000) ≤ ((11305774687 : ℚ) / 25000000000) + (6271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057753227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11305774687 : ℚ) / 25000000000) : ℚ) : ℝ) + ((6271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6271:ℚ)^(-2:ℤ) : ℝ) = ((6271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_816 : ((((28264439893 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6271 < q → q < 6277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6277).mp (by decide +kernel))) hgap
  have hprev := s2L_815
  have hrat : ((28264439893 : ℚ) / 62500000000) ≤ ((113057753227 : ℚ) / 250000000000) + (6277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264439893 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113057753227 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6277:ℚ)^(-2:ℤ) : ℝ) = ((6277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_817 : ((((452231063587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6277 < q → q < 6287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6287).mp (by decide +kernel))) hgap
  have hprev := s2L_816
  have hrat : ((452231063587 : ℚ) / 1000000000000) ≤ ((28264439893 : ℚ) / 62500000000) + (6287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231063587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28264439893 : ℚ) / 62500000000) : ℚ) : ℝ) + ((6287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6287:ℚ)^(-2:ℤ) : ℝ) = ((6287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_818 : ((((45223108879 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6287 < q → q < 6299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6299).mp (by decide +kernel))) hgap
  have hprev := s2L_817
  have hrat : ((45223108879 : ℚ) / 100000000000) ≤ ((452231063587 : ℚ) / 1000000000000) + (6299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223108879 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452231063587 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6299:ℚ)^(-2:ℤ) : ℝ) = ((6299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_819 : ((((452231113977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6299 < q → q < 6301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6301).mp (by decide +kernel))) hgap
  have hprev := s2L_818
  have hrat : ((452231113977 : ℚ) / 1000000000000) ≤ ((45223108879 : ℚ) / 100000000000) + (6301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231113977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223108879 : ℚ) / 100000000000) : ℚ) : ℝ) + ((6301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6301:ℚ)^(-2:ℤ) : ℝ) = ((6301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_820 : ((((113057784771 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6301 < q → q < 6311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6311).mp (by decide +kernel))) hgap
  have hprev := s2L_819
  have hrat : ((113057784771 : ℚ) / 250000000000) ≤ ((452231113977 : ℚ) / 1000000000000) + (6311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057784771 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452231113977 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6311:ℚ)^(-2:ℤ) : ℝ) = ((6311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_821 : ((((452231164143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6311 < q → q < 6317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6317).mp (by decide +kernel))) hgap
  have hprev := s2L_820
  have hrat : ((452231164143 : ℚ) / 1000000000000) ≤ ((113057784771 : ℚ) / 250000000000) + (6317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231164143 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113057784771 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6317:ℚ)^(-2:ℤ) : ℝ) = ((6317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_822 : ((((90446237831 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6317 < q → q < 6323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6323).mp (by decide +kernel))) hgap
  have hprev := s2L_821
  have hrat : ((90446237831 : ℚ) / 200000000000) ≤ ((452231164143 : ℚ) / 1000000000000) + (6323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446237831 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452231164143 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6323:ℚ)^(-2:ℤ) : ℝ) = ((6323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_823 : ((((452231214119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6323 < q → q < 6329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6329).mp (by decide +kernel))) hgap
  have hprev := s2L_822
  have hrat : ((452231214119 : ℚ) / 1000000000000) ≤ ((90446237831 : ℚ) / 200000000000) + (6329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231214119 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446237831 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6329:ℚ)^(-2:ℤ) : ℝ) = ((6329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_824 : ((((22611561951 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6329 < q → q < 6337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6337).mp (by decide +kernel))) hgap
  have hprev := s2L_823
  have hrat : ((22611561951 : ℚ) / 50000000000) ≤ ((452231214119 : ℚ) / 1000000000000) + (6337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611561951 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452231214119 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6337:ℚ)^(-2:ℤ) : ℝ) = ((6337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_825 : ((((226115631937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6337 < q → q < 6343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6343).mp (by decide +kernel))) hgap
  have hprev := s2L_824
  have hrat : ((226115631937 : ℚ) / 500000000000) ≤ ((22611561951 : ℚ) / 50000000000) + (6343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115631937 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22611561951 : ℚ) / 50000000000) : ℚ) : ℝ) + ((6343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6343:ℚ)^(-2:ℤ) : ℝ) = ((6343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_826 : ((((9044625773 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6343 < q → q < 6353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6353).mp (by decide +kernel))) hgap
  have hprev := s2L_825
  have hrat : ((9044625773 : ℚ) / 20000000000) ≤ ((226115631937 : ℚ) / 500000000000) + (6353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044625773 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226115631937 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6353:ℚ)^(-2:ℤ) : ℝ) = ((6353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_827 : ((((452231313379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6359, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6353 < q → q < 6359 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6359).mp (by decide +kernel))) hgap
  have hprev := s2L_826
  have hrat : ((452231313379 : ℚ) / 1000000000000) ≤ ((9044625773 : ℚ) / 20000000000) + (6359:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231313379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044625773 : ℚ) / 20000000000) : ℚ) : ℝ) + ((6359:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6359:ℚ)^(-2:ℤ) : ℝ) = ((6359:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_828 : ((((452231338093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6361, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6359 < q → q < 6361 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6361).mp (by decide +kernel))) hgap
  have hprev := s2L_827
  have hrat : ((452231338093 : ℚ) / 1000000000000) ≤ ((452231313379 : ℚ) / 1000000000000) + (6361:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231338093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231313379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6361:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6361:ℚ)^(-2:ℤ) : ℝ) = ((6361:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_829 : ((((11305784069 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6361 < q → q < 6367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6367).mp (by decide +kernel))) hgap
  have hprev := s2L_828
  have hrat : ((11305784069 : ℚ) / 25000000000) ≤ ((452231338093 : ℚ) / 1000000000000) + (6367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305784069 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452231338093 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6367:ℚ)^(-2:ℤ) : ℝ) = ((6367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_830 : ((((452231387381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6367 < q → q < 6373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6373).mp (by decide +kernel))) hgap
  have hprev := s2L_829
  have hrat : ((452231387381 : ℚ) / 1000000000000) ≤ ((11305784069 : ℚ) / 25000000000) + (6373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231387381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11305784069 : ℚ) / 25000000000) : ℚ) : ℝ) + ((6373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6373:ℚ)^(-2:ℤ) : ℝ) = ((6373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_831 : ((((113057852989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6373 < q → q < 6379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6379).mp (by decide +kernel))) hgap
  have hprev := s2L_830
  have hrat : ((113057852989 : ℚ) / 250000000000) ≤ ((452231387381 : ℚ) / 1000000000000) + (6379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057852989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452231387381 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6379:ℚ)^(-2:ℤ) : ℝ) = ((6379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_832 : ((((226115718227 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6379 < q → q < 6389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6389).mp (by decide +kernel))) hgap
  have hprev := s2L_831
  have hrat : ((226115718227 : ℚ) / 500000000000) ≤ ((113057852989 : ℚ) / 250000000000) + (6389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115718227 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113057852989 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6389:ℚ)^(-2:ℤ) : ℝ) = ((6389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_833 : ((((45223146089 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6389 < q → q < 6397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6397).mp (by decide +kernel))) hgap
  have hprev := s2L_832
  have hrat : ((45223146089 : ℚ) / 100000000000) ≤ ((226115718227 : ℚ) / 500000000000) + (6397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223146089 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226115718227 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6397:ℚ)^(-2:ℤ) : ℝ) = ((6397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_834 : ((((56528935643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6397 < q → q < 6421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6421).mp (by decide +kernel))) hgap
  have hprev := s2L_833
  have hrat : ((56528935643 : ℚ) / 125000000000) ≤ ((45223146089 : ℚ) / 100000000000) + (6421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528935643 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45223146089 : ℚ) / 100000000000) : ℚ) : ℝ) + ((6421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6421:ℚ)^(-2:ℤ) : ℝ) = ((6421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_835 : ((((452231509353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6421 < q → q < 6427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6427).mp (by decide +kernel))) hgap
  have hprev := s2L_834
  have hrat : ((452231509353 : ℚ) / 1000000000000) ≤ ((56528935643 : ℚ) / 125000000000) + (6427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231509353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528935643 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6427:ℚ)^(-2:ℤ) : ℝ) = ((6427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_836 : ((((452231533397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6449, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6427 < q → q < 6449 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6449).mp (by decide +kernel))) hgap
  have hprev := s2L_835
  have hrat : ((452231533397 : ℚ) / 1000000000000) ≤ ((452231509353 : ℚ) / 1000000000000) + (6449:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231533397 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231509353 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6449:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6449:ℚ)^(-2:ℤ) : ℝ) = ((6449:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_837 : ((((226115778713 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6449 < q → q < 6451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6451).mp (by decide +kernel))) hgap
  have hprev := s2L_836
  have hrat : ((226115778713 : ℚ) / 500000000000) ≤ ((452231533397 : ℚ) / 1000000000000) + (6451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115778713 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452231533397 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6451:ℚ)^(-2:ℤ) : ℝ) = ((6451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_838 : ((((226115790661 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6451 < q → q < 6469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6469).mp (by decide +kernel))) hgap
  have hprev := s2L_837
  have hrat : ((226115790661 : ℚ) / 500000000000) ≤ ((226115778713 : ℚ) / 500000000000) + (6469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115790661 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226115778713 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6469:ℚ)^(-2:ℤ) : ℝ) = ((6469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_839 : ((((113057901297 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6469 < q → q < 6473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6473).mp (by decide +kernel))) hgap
  have hprev := s2L_838
  have hrat : ((113057901297 : ℚ) / 250000000000) ≤ ((226115790661 : ℚ) / 500000000000) + (6473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113057901297 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226115790661 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6473:ℚ)^(-2:ℤ) : ℝ) = ((6473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_840 : ((((90446325799 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6473 < q → q < 6481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6481).mp (by decide +kernel))) hgap
  have hprev := s2L_839
  have hrat : ((90446325799 : ℚ) / 200000000000) ≤ ((113057901297 : ℚ) / 250000000000) + (6481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446325799 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113057901297 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6481:ℚ)^(-2:ℤ) : ℝ) = ((6481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_841 : ((((452231652729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6481 < q → q < 6491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6491).mp (by decide +kernel))) hgap
  have hprev := s2L_840
  have hrat : ((452231652729 : ℚ) / 1000000000000) ≤ ((90446325799 : ℚ) / 200000000000) + (6491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231652729 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446325799 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6491:ℚ)^(-2:ℤ) : ℝ) = ((6491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_842 : ((((90446335249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6491 < q → q < 6521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6521).mp (by decide +kernel))) hgap
  have hprev := s2L_841
  have hrat : ((90446335249 : ℚ) / 200000000000) ≤ ((452231652729 : ℚ) / 1000000000000) + (6521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446335249 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452231652729 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6521:ℚ)^(-2:ℤ) : ℝ) = ((6521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_843 : ((((452231699703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6521 < q → q < 6529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6529).mp (by decide +kernel))) hgap
  have hprev := s2L_842
  have hrat : ((452231699703 : ℚ) / 1000000000000) ≤ ((90446335249 : ℚ) / 200000000000) + (6529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231699703 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446335249 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6529:ℚ)^(-2:ℤ) : ℝ) = ((6529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_844 : ((((452231723033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6529 < q → q < 6547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6547).mp (by decide +kernel))) hgap
  have hprev := s2L_843
  have hrat : ((452231723033 : ℚ) / 1000000000000) ≤ ((452231699703 : ℚ) / 1000000000000) + (6547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231723033 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231699703 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6547:ℚ)^(-2:ℤ) : ℝ) = ((6547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_845 : ((((226115873167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6547 < q → q < 6551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6551).mp (by decide +kernel))) hgap
  have hprev := s2L_844
  have hrat : ((226115873167 : ℚ) / 500000000000) ≤ ((452231723033 : ℚ) / 1000000000000) + (6551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226115873167 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452231723033 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6551:ℚ)^(-2:ℤ) : ℝ) = ((6551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_846 : ((((452231769621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6551 < q → q < 6553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6553).mp (by decide +kernel))) hgap
  have hprev := s2L_845
  have hrat : ((452231769621 : ℚ) / 1000000000000) ≤ ((226115873167 : ℚ) / 500000000000) + (6553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231769621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226115873167 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6553:ℚ)^(-2:ℤ) : ℝ) = ((6553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_847 : ((((452231792837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6553 < q → q < 6563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6563).mp (by decide +kernel))) hgap
  have hprev := s2L_846
  have hrat : ((452231792837 : ℚ) / 1000000000000) ≤ ((452231769621 : ℚ) / 1000000000000) + (6563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231792837 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231769621 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6563:ℚ)^(-2:ℤ) : ℝ) = ((6563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_848 : ((((452231816011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6563 < q → q < 6569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6569).mp (by decide +kernel))) hgap
  have hprev := s2L_847
  have hrat : ((452231816011 : ℚ) / 1000000000000) ≤ ((452231792837 : ℚ) / 1000000000000) + (6569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231816011 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231792837 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6569:ℚ)^(-2:ℤ) : ℝ) = ((6569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_849 : ((((45223183917 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6571, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6569 < q → q < 6571 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6571).mp (by decide +kernel))) hgap
  have hprev := s2L_848
  have hrat : ((45223183917 : ℚ) / 100000000000) ≤ ((452231816011 : ℚ) / 1000000000000) + (6571:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223183917 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452231816011 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6571:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6571:ℚ)^(-2:ℤ) : ℝ) = ((6571:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_850 : ((((452231862287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6571 < q → q < 6577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6577).mp (by decide +kernel))) hgap
  have hprev := s2L_849
  have hrat : ((452231862287 : ℚ) / 1000000000000) ≤ ((45223183917 : ℚ) / 100000000000) + (6577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231862287 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223183917 : ℚ) / 100000000000) : ℚ) : ℝ) + ((6577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6577:ℚ)^(-2:ℤ) : ℝ) = ((6577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_851 : ((((7066123209 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6577 < q → q < 6581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6581).mp (by decide +kernel))) hgap
  have hprev := s2L_850
  have hrat : ((7066123209 : ℚ) / 15625000000) ≤ ((452231862287 : ℚ) / 1000000000000) + (6581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066123209 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((452231862287 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6581:ℚ)^(-2:ℤ) : ℝ) = ((6581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_852 : ((((452231908339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6581 < q → q < 6599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6599).mp (by decide +kernel))) hgap
  have hprev := s2L_851
  have hrat : ((452231908339 : ℚ) / 1000000000000) ≤ ((7066123209 : ℚ) / 15625000000) + (6599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231908339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066123209 : ℚ) / 15625000000) : ℚ) : ℝ) + ((6599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6599:ℚ)^(-2:ℤ) : ℝ) = ((6599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_853 : ((((452231931247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6599 < q → q < 6607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6607).mp (by decide +kernel))) hgap
  have hprev := s2L_852
  have hrat : ((452231931247 : ℚ) / 1000000000000) ≤ ((452231908339 : ℚ) / 1000000000000) + (6607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231931247 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452231908339 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6607:ℚ)^(-2:ℤ) : ℝ) = ((6607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_854 : ((((56528994259 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6607 < q → q < 6619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6619).mp (by decide +kernel))) hgap
  have hprev := s2L_853
  have hrat : ((56528994259 : ℚ) / 125000000000) ≤ ((452231931247 : ℚ) / 1000000000000) + (6619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56528994259 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452231931247 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6619:ℚ)^(-2:ℤ) : ℝ) = ((6619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_855 : ((((452231976773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6619 < q → q < 6637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6637).mp (by decide +kernel))) hgap
  have hprev := s2L_854
  have hrat : ((452231976773 : ℚ) / 1000000000000) ≤ ((56528994259 : ℚ) / 125000000000) + (6637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452231976773 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56528994259 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6637:ℚ)^(-2:ℤ) : ℝ) = ((6637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_856 : ((((90446399873 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6637 < q → q < 6653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6653).mp (by decide +kernel))) hgap
  have hprev := s2L_855
  have hrat : ((90446399873 : ℚ) / 200000000000) ≤ ((452231976773 : ℚ) / 1000000000000) + (6653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446399873 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452231976773 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6653:ℚ)^(-2:ℤ) : ℝ) = ((6653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_857 : ((((113058005479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6653 < q → q < 6659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6659).mp (by decide +kernel))) hgap
  have hprev := s2L_856
  have hrat : ((113058005479 : ℚ) / 250000000000) ≤ ((90446399873 : ℚ) / 200000000000) + (6659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058005479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90446399873 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6659:ℚ)^(-2:ℤ) : ℝ) = ((6659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_858 : ((((226116022227 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6659 < q → q < 6661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6661).mp (by decide +kernel))) hgap
  have hprev := s2L_857
  have hrat : ((226116022227 : ℚ) / 500000000000) ≤ ((113058005479 : ℚ) / 250000000000) + (6661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116022227 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058005479 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6661:ℚ)^(-2:ℤ) : ℝ) = ((6661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_859 : ((((452232066911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6661 < q → q < 6673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6673).mp (by decide +kernel))) hgap
  have hprev := s2L_858
  have hrat : ((452232066911 : ℚ) / 1000000000000) ≤ ((226116022227 : ℚ) / 500000000000) + (6673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232066911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116022227 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6673:ℚ)^(-2:ℤ) : ℝ) = ((6673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_860 : ((((452232089327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6673 < q → q < 6679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6679).mp (by decide +kernel))) hgap
  have hprev := s2L_859
  have hrat : ((452232089327 : ℚ) / 1000000000000) ≤ ((452232066911 : ℚ) / 1000000000000) + (6679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232089327 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232066911 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6679:ℚ)^(-2:ℤ) : ℝ) = ((6679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_861 : ((((452232111677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6679 < q → q < 6689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6689).mp (by decide +kernel))) hgap
  have hprev := s2L_860
  have hrat : ((452232111677 : ℚ) / 1000000000000) ≤ ((452232089327 : ℚ) / 1000000000000) + (6689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232111677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232089327 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6689:ℚ)^(-2:ℤ) : ℝ) = ((6689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_862 : ((((452232134013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6689 < q → q < 6691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6691).mp (by decide +kernel))) hgap
  have hprev := s2L_861
  have hrat : ((452232134013 : ℚ) / 1000000000000) ≤ ((452232111677 : ℚ) / 1000000000000) + (6691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232134013 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232111677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6691:ℚ)^(-2:ℤ) : ℝ) = ((6691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_863 : ((((452232156283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6691 < q → q < 6701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6701).mp (by decide +kernel))) hgap
  have hprev := s2L_862
  have hrat : ((452232156283 : ℚ) / 1000000000000) ≤ ((452232134013 : ℚ) / 1000000000000) + (6701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232156283 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232134013 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6701:ℚ)^(-2:ℤ) : ℝ) = ((6701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_864 : ((((452232178539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6701 < q → q < 6703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6703).mp (by decide +kernel))) hgap
  have hprev := s2L_863
  have hrat : ((452232178539 : ℚ) / 1000000000000) ≤ ((452232156283 : ℚ) / 1000000000000) + (6703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232178539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232156283 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6703:ℚ)^(-2:ℤ) : ℝ) = ((6703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_865 : ((((90446440151 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6703 < q → q < 6709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6709).mp (by decide +kernel))) hgap
  have hprev := s2L_864
  have hrat : ((90446440151 : ℚ) / 200000000000) ≤ ((452232178539 : ℚ) / 1000000000000) + (6709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446440151 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452232178539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6709:ℚ)^(-2:ℤ) : ℝ) = ((6709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_866 : ((((90446444581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6709 < q → q < 6719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6719).mp (by decide +kernel))) hgap
  have hprev := s2L_865
  have hrat : ((90446444581 : ℚ) / 200000000000) ≤ ((90446440151 : ℚ) / 200000000000) + (6719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446444581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90446440151 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6719:ℚ)^(-2:ℤ) : ℝ) = ((6719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_867 : ((((452232244963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6719 < q → q < 6733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6733).mp (by decide +kernel))) hgap
  have hprev := s2L_866
  have hrat : ((452232244963 : ℚ) / 1000000000000) ≤ ((90446444581 : ℚ) / 200000000000) + (6733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232244963 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446444581 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6733:ℚ)^(-2:ℤ) : ℝ) = ((6733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_868 : ((((90446453399 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6733 < q → q < 6737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6737).mp (by decide +kernel))) hgap
  have hprev := s2L_867
  have hrat : ((90446453399 : ℚ) / 200000000000) ≤ ((452232244963 : ℚ) / 1000000000000) + (6737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446453399 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452232244963 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6737:ℚ)^(-2:ℤ) : ℝ) = ((6737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_869 : ((((452232288871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6737 < q → q < 6761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6761).mp (by decide +kernel))) hgap
  have hprev := s2L_868
  have hrat : ((452232288871 : ℚ) / 1000000000000) ≤ ((90446453399 : ℚ) / 200000000000) + (6761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232288871 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446453399 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6761:ℚ)^(-2:ℤ) : ℝ) = ((6761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_870 : ((((226116155367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6761 < q → q < 6763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6763).mp (by decide +kernel))) hgap
  have hprev := s2L_869
  have hrat : ((226116155367 : ℚ) / 500000000000) ≤ ((452232288871 : ℚ) / 1000000000000) + (6763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116155367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452232288871 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6763:ℚ)^(-2:ℤ) : ℝ) = ((6763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_871 : ((((226116166247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6763 < q → q < 6779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6779).mp (by decide +kernel))) hgap
  have hprev := s2L_870
  have hrat : ((226116166247 : ℚ) / 500000000000) ≤ ((226116155367 : ℚ) / 500000000000) + (6779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116166247 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116155367 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6779:ℚ)^(-2:ℤ) : ℝ) = ((6779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_872 : ((((452232354241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6779 < q → q < 6781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6781).mp (by decide +kernel))) hgap
  have hprev := s2L_871
  have hrat : ((452232354241 : ℚ) / 1000000000000) ≤ ((226116166247 : ℚ) / 500000000000) + (6781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232354241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116166247 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6781:ℚ)^(-2:ℤ) : ℝ) = ((6781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_873 : ((((113058093981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6781 < q → q < 6791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6791).mp (by decide +kernel))) hgap
  have hprev := s2L_872
  have hrat : ((113058093981 : ℚ) / 250000000000) ≤ ((452232354241 : ℚ) / 1000000000000) + (6791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058093981 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452232354241 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6791:ℚ)^(-2:ℤ) : ℝ) = ((6791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_874 : ((((226116198797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6791 < q → q < 6793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6793).mp (by decide +kernel))) hgap
  have hprev := s2L_873
  have hrat : ((226116198797 : ℚ) / 500000000000) ≤ ((113058093981 : ℚ) / 250000000000) + (6793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116198797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058093981 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6793:ℚ)^(-2:ℤ) : ℝ) = ((6793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_875 : ((((452232419201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6793 < q → q < 6803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6803).mp (by decide +kernel))) hgap
  have hprev := s2L_874
  have hrat : ((452232419201 : ℚ) / 1000000000000) ≤ ((226116198797 : ℚ) / 500000000000) + (6803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232419201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116198797 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6803:ℚ)^(-2:ℤ) : ℝ) = ((6803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_876 : ((((452232440681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6803 < q → q < 6823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6823).mp (by decide +kernel))) hgap
  have hprev := s2L_875
  have hrat : ((452232440681 : ℚ) / 1000000000000) ≤ ((452232419201 : ℚ) / 1000000000000) + (6823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232440681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232419201 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6823:ℚ)^(-2:ℤ) : ℝ) = ((6823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_877 : ((((56529057767 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6823 < q → q < 6827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6827).mp (by decide +kernel))) hgap
  have hprev := s2L_876
  have hrat : ((56529057767 : ℚ) / 125000000000) ≤ ((452232440681 : ℚ) / 1000000000000) + (6827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529057767 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452232440681 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6827:ℚ)^(-2:ℤ) : ℝ) = ((6827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_878 : ((((452232483579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6827 < q → q < 6829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6829).mp (by decide +kernel))) hgap
  have hprev := s2L_877
  have hrat : ((452232483579 : ℚ) / 1000000000000) ≤ ((56529057767 : ℚ) / 125000000000) + (6829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232483579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529057767 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6829:ℚ)^(-2:ℤ) : ℝ) = ((6829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_879 : ((((113058126249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6829 < q → q < 6833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6833).mp (by decide +kernel))) hgap
  have hprev := s2L_878
  have hrat : ((113058126249 : ℚ) / 250000000000) ≤ ((452232483579 : ℚ) / 1000000000000) + (6833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058126249 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452232483579 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6833:ℚ)^(-2:ℤ) : ℝ) = ((6833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_880 : ((((452232526363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6833 < q → q < 6841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6841).mp (by decide +kernel))) hgap
  have hprev := s2L_879
  have hrat : ((452232526363 : ℚ) / 1000000000000) ≤ ((113058126249 : ℚ) / 250000000000) + (6841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232526363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058126249 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6841:ℚ)^(-2:ℤ) : ℝ) = ((6841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_881 : ((((452232547631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6841 < q → q < 6857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6857).mp (by decide +kernel))) hgap
  have hprev := s2L_880
  have hrat : ((452232547631 : ℚ) / 1000000000000) ≤ ((452232526363 : ℚ) / 1000000000000) + (6857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232547631 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232526363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6857:ℚ)^(-2:ℤ) : ℝ) = ((6857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_882 : ((((226116284431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6857 < q → q < 6863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6863).mp (by decide +kernel))) hgap
  have hprev := s2L_881
  have hrat : ((226116284431 : ℚ) / 500000000000) ≤ ((452232547631 : ℚ) / 1000000000000) + (6863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116284431 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452232547631 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6863:ℚ)^(-2:ℤ) : ℝ) = ((6863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_883 : ((((56529073757 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6869, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6863 < q → q < 6869 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6869).mp (by decide +kernel))) hgap
  have hprev := s2L_882
  have hrat : ((56529073757 : ℚ) / 125000000000) ≤ ((226116284431 : ℚ) / 500000000000) + (6869:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529073757 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226116284431 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6869:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6869:ℚ)^(-2:ℤ) : ℝ) = ((6869:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_884 : ((((452232611237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6869 < q → q < 6871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6871).mp (by decide +kernel))) hgap
  have hprev := s2L_883
  have hrat : ((452232611237 : ℚ) / 1000000000000) ≤ ((56529073757 : ℚ) / 125000000000) + (6871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232611237 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529073757 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6871:ℚ)^(-2:ℤ) : ℝ) = ((6871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_885 : ((((56529079043 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6871 < q → q < 6883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6883).mp (by decide +kernel))) hgap
  have hprev := s2L_884
  have hrat : ((56529079043 : ℚ) / 125000000000) ≤ ((452232611237 : ℚ) / 1000000000000) + (6883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529079043 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452232611237 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6883:ℚ)^(-2:ℤ) : ℝ) = ((6883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_886 : ((((226116326677 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6899, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6883 < q → q < 6899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6899).mp (by decide +kernel))) hgap
  have hprev := s2L_885
  have hrat : ((226116326677 : ℚ) / 500000000000) ≤ ((56529079043 : ℚ) / 125000000000) + (6899:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116326677 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529079043 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6899:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6899:ℚ)^(-2:ℤ) : ℝ) = ((6899:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_887 : ((((90446534863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6899 < q → q < 6907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6907).mp (by decide +kernel))) hgap
  have hprev := s2L_886
  have hrat : ((90446534863 : ℚ) / 200000000000) ≤ ((226116326677 : ℚ) / 500000000000) + (6907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446534863 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226116326677 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6907:ℚ)^(-2:ℤ) : ℝ) = ((6907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_888 : ((((113058173813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6907 < q → q < 6911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6911).mp (by decide +kernel))) hgap
  have hprev := s2L_887
  have hrat : ((113058173813 : ℚ) / 250000000000) ≤ ((90446534863 : ℚ) / 200000000000) + (6911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058173813 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90446534863 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6911:ℚ)^(-2:ℤ) : ℝ) = ((6911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_889 : ((((56529089519 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6911 < q → q < 6917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6917).mp (by decide +kernel))) hgap
  have hprev := s2L_888
  have hrat : ((56529089519 : ℚ) / 125000000000) ≤ ((113058173813 : ℚ) / 250000000000) + (6917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529089519 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113058173813 : ℚ) / 250000000000) : ℚ) : ℝ) + ((6917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6917:ℚ)^(-2:ℤ) : ℝ) = ((6917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_890 : ((((56529092109 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6947, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6917 < q → q < 6947 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6947).mp (by decide +kernel))) hgap
  have hprev := s2L_889
  have hrat : ((56529092109 : ℚ) / 125000000000) ≤ ((56529089519 : ℚ) / 125000000000) + (6947:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529092109 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((56529089519 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6947:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6947:ℚ)^(-2:ℤ) : ℝ) = ((6947:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_891 : ((((22611637879 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6947 < q → q < 6949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6949).mp (by decide +kernel))) hgap
  have hprev := s2L_890
  have hrat : ((22611637879 : ℚ) / 50000000000) ≤ ((56529092109 : ℚ) / 125000000000) + (6949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611637879 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56529092109 : ℚ) / 125000000000) : ℚ) : ℝ) + ((6949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6949:ℚ)^(-2:ℤ) : ℝ) = ((6949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_892 : ((((452232778229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6949 < q → q < 6959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6959).mp (by decide +kernel))) hgap
  have hprev := s2L_891
  have hrat : ((452232778229 : ℚ) / 1000000000000) ≤ ((22611637879 : ℚ) / 50000000000) + (6959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232778229 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22611637879 : ℚ) / 50000000000) : ℚ) : ℝ) + ((6959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6959:ℚ)^(-2:ℤ) : ℝ) = ((6959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_893 : ((((226116399433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6961, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6959 < q → q < 6961 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6961).mp (by decide +kernel))) hgap
  have hprev := s2L_892
  have hrat : ((226116399433 : ℚ) / 500000000000) ≤ ((452232778229 : ℚ) / 1000000000000) + (6961:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116399433 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452232778229 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6961:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6961:ℚ)^(-2:ℤ) : ℝ) = ((6961:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_894 : ((((452232819467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6961 < q → q < 6967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6967).mp (by decide +kernel))) hgap
  have hprev := s2L_893
  have hrat : ((452232819467 : ℚ) / 1000000000000) ≤ ((226116399433 : ℚ) / 500000000000) + (6967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232819467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116399433 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6967:ℚ)^(-2:ℤ) : ℝ) = ((6967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_895 : ((((90446568009 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6967 < q → q < 6971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6971).mp (by decide +kernel))) hgap
  have hprev := s2L_894
  have hrat : ((90446568009 : ℚ) / 200000000000) ≤ ((452232819467 : ℚ) / 1000000000000) + (6971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446568009 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452232819467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6971:ℚ)^(-2:ℤ) : ℝ) = ((6971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_896 : ((((452232860587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6977, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6971 < q → q < 6977 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6977).mp (by decide +kernel))) hgap
  have hprev := s2L_895
  have hrat : ((452232860587 : ℚ) / 1000000000000) ≤ ((90446568009 : ℚ) / 200000000000) + (6977:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232860587 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446568009 : ℚ) / 200000000000) : ℚ) : ℝ) + ((6977:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6977:ℚ)^(-2:ℤ) : ℝ) = ((6977:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_897 : ((((226116440547 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6977 < q → q < 6983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6983).mp (by decide +kernel))) hgap
  have hprev := s2L_896
  have hrat : ((226116440547 : ℚ) / 500000000000) ≤ ((452232860587 : ℚ) / 1000000000000) + (6983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116440547 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452232860587 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((6983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6983:ℚ)^(-2:ℤ) : ℝ) = ((6983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_898 : ((((226116450777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6991, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6983 < q → q < 6991 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6991).mp (by decide +kernel))) hgap
  have hprev := s2L_897
  have hrat : ((226116450777 : ℚ) / 500000000000) ≤ ((226116440547 : ℚ) / 500000000000) + (6991:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116450777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116440547 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6991:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6991:ℚ)^(-2:ℤ) : ℝ) = ((6991:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_899 : ((((452232921979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 6997, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6991 < q → q < 6997 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 6997).mp (by decide +kernel))) hgap
  have hprev := s2L_898
  have hrat : ((452232921979 : ℚ) / 1000000000000) ≤ ((226116450777 : ℚ) / 500000000000) + (6997:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232921979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116450777 : ℚ) / 500000000000) : ℚ) : ℝ) + ((6997:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((6997:ℚ)^(-2:ℤ) : ℝ) = ((6997:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_900 : ((((452232942381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 6997 < q → q < 7001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7001).mp (by decide +kernel))) hgap
  have hprev := s2L_899
  have hrat : ((452232942381 : ℚ) / 1000000000000) ≤ ((452232921979 : ℚ) / 1000000000000) + (7001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232942381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232921979 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7001:ℚ)^(-2:ℤ) : ℝ) = ((7001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_901 : ((((452232962713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7001 < q → q < 7013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7013).mp (by decide +kernel))) hgap
  have hprev := s2L_900
  have hrat : ((452232962713 : ℚ) / 1000000000000) ≤ ((452232942381 : ℚ) / 1000000000000) + (7013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452232962713 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452232942381 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7013:ℚ)^(-2:ℤ) : ℝ) = ((7013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_902 : ((((45223298301 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7019, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7013 < q → q < 7019 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7019).mp (by decide +kernel))) hgap
  have hprev := s2L_901
  have hrat : ((45223298301 : ℚ) / 100000000000) ≤ ((452232962713 : ℚ) / 1000000000000) + (7019:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223298301 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452232962713 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7019:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7019:ℚ)^(-2:ℤ) : ℝ) = ((7019:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_903 : ((((452233003261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7019 < q → q < 7027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7027).mp (by decide +kernel))) hgap
  have hprev := s2L_902
  have hrat : ((452233003261 : ℚ) / 1000000000000) ≤ ((45223298301 : ℚ) / 100000000000) + (7027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233003261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223298301 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7027:ℚ)^(-2:ℤ) : ℝ) = ((7027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_904 : ((((452233023443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7027 < q → q < 7039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7039).mp (by decide +kernel))) hgap
  have hprev := s2L_903
  have hrat : ((452233023443 : ℚ) / 1000000000000) ≤ ((452233003261 : ℚ) / 1000000000000) + (7039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233023443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233003261 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7039:ℚ)^(-2:ℤ) : ℝ) = ((7039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_905 : ((((226116521801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7039 < q → q < 7043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7043).mp (by decide +kernel))) hgap
  have hprev := s2L_904
  have hrat : ((226116521801 : ℚ) / 500000000000) ≤ ((452233023443 : ℚ) / 1000000000000) + (7043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116521801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452233023443 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7043:ℚ)^(-2:ℤ) : ℝ) = ((7043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_906 : ((((452233063681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7043 < q → q < 7057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7057).mp (by decide +kernel))) hgap
  have hprev := s2L_905
  have hrat : ((452233063681 : ℚ) / 1000000000000) ≤ ((226116521801 : ℚ) / 500000000000) + (7057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233063681 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116521801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7057:ℚ)^(-2:ℤ) : ℝ) = ((7057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_907 : ((((113058270923 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7057 < q → q < 7069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7069).mp (by decide +kernel))) hgap
  have hprev := s2L_906
  have hrat : ((113058270923 : ℚ) / 250000000000) ≤ ((452233063681 : ℚ) / 1000000000000) + (7069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058270923 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233063681 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7069:ℚ)^(-2:ℤ) : ℝ) = ((7069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_908 : ((((452233103647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7069 < q → q < 7079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7079).mp (by decide +kernel))) hgap
  have hprev := s2L_907
  have hrat : ((452233103647 : ℚ) / 1000000000000) ≤ ((113058270923 : ℚ) / 250000000000) + (7079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233103647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058270923 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7079:ℚ)^(-2:ℤ) : ℝ) = ((7079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_909 : ((((452233123467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7079 < q → q < 7103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7103).mp (by decide +kernel))) hgap
  have hprev := s2L_908
  have hrat : ((452233123467 : ℚ) / 1000000000000) ≤ ((452233103647 : ℚ) / 1000000000000) + (7103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233123467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233103647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7103:ℚ)^(-2:ℤ) : ℝ) = ((7103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_910 : ((((226116571627 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7103 < q → q < 7109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7109).mp (by decide +kernel))) hgap
  have hprev := s2L_909
  have hrat : ((226116571627 : ℚ) / 500000000000) ≤ ((452233123467 : ℚ) / 1000000000000) + (7109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116571627 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452233123467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7109:ℚ)^(-2:ℤ) : ℝ) = ((7109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_911 : ((((226116581487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7109 < q → q < 7121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7121).mp (by decide +kernel))) hgap
  have hprev := s2L_910
  have hrat : ((226116581487 : ℚ) / 500000000000) ≤ ((226116571627 : ℚ) / 500000000000) + (7121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116581487 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116571627 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7121:ℚ)^(-2:ℤ) : ℝ) = ((7121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_912 : ((((452233182661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7121 < q → q < 7127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7127).mp (by decide +kernel))) hgap
  have hprev := s2L_911
  have hrat : ((452233182661 : ℚ) / 1000000000000) ≤ ((226116581487 : ℚ) / 500000000000) + (7127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233182661 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116581487 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7127:ℚ)^(-2:ℤ) : ℝ) = ((7127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_913 : ((((452233202337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7129, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7127 < q → q < 7129 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7129).mp (by decide +kernel))) hgap
  have hprev := s2L_912
  have hrat : ((452233202337 : ℚ) / 1000000000000) ≤ ((452233182661 : ℚ) / 1000000000000) + (7129:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233202337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233182661 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7129:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7129:ℚ)^(-2:ℤ) : ℝ) = ((7129:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_914 : ((((113058305473 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7129 < q → q < 7151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7151).mp (by decide +kernel))) hgap
  have hprev := s2L_913
  have hrat : ((113058305473 : ℚ) / 250000000000) ≤ ((452233202337 : ℚ) / 1000000000000) + (7151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058305473 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233202337 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7151:ℚ)^(-2:ℤ) : ℝ) = ((7151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_915 : ((((452233241403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7151 < q → q < 7159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7159).mp (by decide +kernel))) hgap
  have hprev := s2L_914
  have hrat : ((452233241403 : ℚ) / 1000000000000) ≤ ((113058305473 : ℚ) / 250000000000) + (7159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233241403 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058305473 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7159:ℚ)^(-2:ℤ) : ℝ) = ((7159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_916 : ((((28264578801 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7159 < q → q < 7177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7177).mp (by decide +kernel))) hgap
  have hprev := s2L_915
  have hrat : ((28264578801 : ℚ) / 62500000000) ≤ ((452233241403 : ℚ) / 1000000000000) + (7177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264578801 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452233241403 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7177:ℚ)^(-2:ℤ) : ℝ) = ((7177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_917 : ((((18089331207 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7177 < q → q < 7187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7187).mp (by decide +kernel))) hgap
  have hprev := s2L_916
  have hrat : ((18089331207 : ℚ) / 40000000000) ≤ ((28264578801 : ℚ) / 62500000000) + (7187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089331207 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((28264578801 : ℚ) / 62500000000) : ℚ) : ℝ) + ((7187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7187:ℚ)^(-2:ℤ) : ℝ) = ((7187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_918 : ((((226116649751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7187 < q → q < 7193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7193).mp (by decide +kernel))) hgap
  have hprev := s2L_917
  have hrat : ((226116649751 : ℚ) / 500000000000) ≤ ((18089331207 : ℚ) / 40000000000) + (7193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116649751 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089331207 : ℚ) / 40000000000) : ℚ) : ℝ) + ((7193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7193:ℚ)^(-2:ℤ) : ℝ) = ((7193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_919 : ((((226116659377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7207, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7193 < q → q < 7207 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7207).mp (by decide +kernel))) hgap
  have hprev := s2L_918
  have hrat : ((226116659377 : ℚ) / 500000000000) ≤ ((226116649751 : ℚ) / 500000000000) + (7207:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116659377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116649751 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7207:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7207:ℚ)^(-2:ℤ) : ℝ) = ((7207:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_920 : ((((90446667597 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7207 < q → q < 7211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7211).mp (by decide +kernel))) hgap
  have hprev := s2L_919
  have hrat : ((90446667597 : ℚ) / 200000000000) ≤ ((226116659377 : ℚ) / 500000000000) + (7211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446667597 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226116659377 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7211:ℚ)^(-2:ℤ) : ℝ) = ((7211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_921 : ((((90446671441 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7213, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7211 < q → q < 7213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7213).mp (by decide +kernel))) hgap
  have hprev := s2L_920
  have hrat : ((90446671441 : ℚ) / 200000000000) ≤ ((90446667597 : ℚ) / 200000000000) + (7213:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446671441 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90446667597 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7213:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7213:ℚ)^(-2:ℤ) : ℝ) = ((7213:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_922 : ((((452233376393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7213 < q → q < 7219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7219).mp (by decide +kernel))) hgap
  have hprev := s2L_921
  have hrat : ((452233376393 : ℚ) / 1000000000000) ≤ ((90446671441 : ℚ) / 200000000000) + (7219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233376393 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446671441 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7219:ℚ)^(-2:ℤ) : ℝ) = ((7219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_923 : ((((56529174441 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7219 < q → q < 7229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7229).mp (by decide +kernel))) hgap
  have hprev := s2L_922
  have hrat : ((56529174441 : ℚ) / 125000000000) ≤ ((452233376393 : ℚ) / 1000000000000) + (7229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529174441 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452233376393 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7229:ℚ)^(-2:ℤ) : ℝ) = ((7229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_924 : ((((452233414621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7229 < q → q < 7237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7237).mp (by decide +kernel))) hgap
  have hprev := s2L_923
  have hrat : ((452233414621 : ℚ) / 1000000000000) ≤ ((56529174441 : ℚ) / 125000000000) + (7237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233414621 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529174441 : ℚ) / 125000000000) : ℚ) : ℝ) + ((7237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7237:ℚ)^(-2:ℤ) : ℝ) = ((7237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_925 : ((((226116716841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7237 < q → q < 7243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7243).mp (by decide +kernel))) hgap
  have hprev := s2L_924
  have hrat : ((226116716841 : ℚ) / 500000000000) ≤ ((452233414621 : ℚ) / 1000000000000) + (7243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116716841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452233414621 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7243:ℚ)^(-2:ℤ) : ℝ) = ((7243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_926 : ((((226116726361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7243 < q → q < 7247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7247).mp (by decide +kernel))) hgap
  have hprev := s2L_925
  have hrat : ((226116726361 : ℚ) / 500000000000) ≤ ((226116716841 : ℚ) / 500000000000) + (7247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116726361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116716841 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7247:ℚ)^(-2:ℤ) : ℝ) = ((7247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_927 : ((((452233471731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7247 < q → q < 7253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7253).mp (by decide +kernel))) hgap
  have hprev := s2L_926
  have hrat : ((452233471731 : ℚ) / 1000000000000) ≤ ((226116726361 : ℚ) / 500000000000) + (7253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233471731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116726361 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7253:ℚ)^(-2:ℤ) : ℝ) = ((7253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_928 : ((((452233490583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7253 < q → q < 7283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7283).mp (by decide +kernel))) hgap
  have hprev := s2L_927
  have hrat : ((452233490583 : ℚ) / 1000000000000) ≤ ((452233471731 : ℚ) / 1000000000000) + (7283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233490583 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233471731 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7283:ℚ)^(-2:ℤ) : ℝ) = ((7283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_929 : ((((452233509363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7283 < q → q < 7297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7297).mp (by decide +kernel))) hgap
  have hprev := s2L_928
  have hrat : ((452233509363 : ℚ) / 1000000000000) ≤ ((452233490583 : ℚ) / 1000000000000) + (7297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233509363 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233490583 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7297:ℚ)^(-2:ℤ) : ℝ) = ((7297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_930 : ((((113058382023 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7307, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7297 < q → q < 7307 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7307).mp (by decide +kernel))) hgap
  have hprev := s2L_929
  have hrat : ((113058382023 : ℚ) / 250000000000) ≤ ((452233509363 : ℚ) / 1000000000000) + (7307:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058382023 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233509363 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7307:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7307:ℚ)^(-2:ℤ) : ℝ) = ((7307:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_931 : ((((452233546811 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7307 < q → q < 7309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7309).mp (by decide +kernel))) hgap
  have hprev := s2L_930
  have hrat : ((452233546811 : ℚ) / 1000000000000) ≤ ((113058382023 : ℚ) / 250000000000) + (7309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233546811 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058382023 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7309:ℚ)^(-2:ℤ) : ℝ) = ((7309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_932 : ((((113058391367 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7309 < q → q < 7321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7321).mp (by decide +kernel))) hgap
  have hprev := s2L_931
  have hrat : ((113058391367 : ℚ) / 250000000000) ≤ ((452233546811 : ℚ) / 1000000000000) + (7321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058391367 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233546811 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7321:ℚ)^(-2:ℤ) : ℝ) = ((7321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_933 : ((((226116792037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7321 < q → q < 7331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7331).mp (by decide +kernel))) hgap
  have hprev := s2L_932
  have hrat : ((226116792037 : ℚ) / 500000000000) ≤ ((113058391367 : ℚ) / 250000000000) + (7331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116792037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058391367 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7331:ℚ)^(-2:ℤ) : ℝ) = ((7331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_934 : ((((45223360267 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7331 < q → q < 7333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7333).mp (by decide +kernel))) hgap
  have hprev := s2L_933
  have hrat : ((45223360267 : ℚ) / 100000000000) ≤ ((226116792037 : ℚ) / 500000000000) + (7333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223360267 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226116792037 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7333:ℚ)^(-2:ℤ) : ℝ) = ((7333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_935 : ((((90446724237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7333 < q → q < 7349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7349).mp (by decide +kernel))) hgap
  have hprev := s2L_934
  have hrat : ((90446724237 : ℚ) / 200000000000) ≤ ((45223360267 : ℚ) / 100000000000) + (7349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446724237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45223360267 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7349:ℚ)^(-2:ℤ) : ℝ) = ((7349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_936 : ((((45223363969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7349 < q → q < 7351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7351).mp (by decide +kernel))) hgap
  have hprev := s2L_935
  have hrat : ((45223363969 : ℚ) / 100000000000) ≤ ((90446724237 : ℚ) / 200000000000) + (7351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223363969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90446724237 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7351:ℚ)^(-2:ℤ) : ℝ) = ((7351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_937 : ((((90446731621 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7351 < q → q < 7369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7369).mp (by decide +kernel))) hgap
  have hprev := s2L_936
  have hrat : ((90446731621 : ℚ) / 200000000000) ≤ ((45223363969 : ℚ) / 100000000000) + (7369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446731621 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45223363969 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7369:ℚ)^(-2:ℤ) : ℝ) = ((7369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_938 : ((((452233676401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7369 < q → q < 7393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7393).mp (by decide +kernel))) hgap
  have hprev := s2L_937
  have hrat : ((452233676401 : ℚ) / 1000000000000) ≤ ((90446731621 : ℚ) / 200000000000) + (7393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233676401 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446731621 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7393:ℚ)^(-2:ℤ) : ℝ) = ((7393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_939 : ((((28264605913 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7393 < q → q < 7411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7411).mp (by decide +kernel))) hgap
  have hprev := s2L_938
  have hrat : ((28264605913 : ℚ) / 62500000000) ≤ ((452233676401 : ℚ) / 1000000000000) + (7411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264605913 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452233676401 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7411:ℚ)^(-2:ℤ) : ℝ) = ((7411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_940 : ((((90446742557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7411 < q → q < 7417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7417).mp (by decide +kernel))) hgap
  have hprev := s2L_939
  have hrat : ((90446742557 : ℚ) / 200000000000) ≤ ((28264605913 : ℚ) / 62500000000) + (7417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446742557 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28264605913 : ℚ) / 62500000000) : ℚ) : ℝ) + ((7417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7417:ℚ)^(-2:ℤ) : ℝ) = ((7417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_941 : ((((113058432721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7417 < q → q < 7433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7433).mp (by decide +kernel))) hgap
  have hprev := s2L_940
  have hrat : ((113058432721 : ℚ) / 250000000000) ≤ ((90446742557 : ℚ) / 200000000000) + (7433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058432721 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90446742557 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7433:ℚ)^(-2:ℤ) : ℝ) = ((7433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_942 : ((((14132304653 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7433 < q → q < 7451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7451).mp (by decide +kernel))) hgap
  have hprev := s2L_941
  have hrat : ((14132304653 : ℚ) / 31250000000) ≤ ((113058432721 : ℚ) / 250000000000) + (7451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132304653 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113058432721 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7451:ℚ)^(-2:ℤ) : ℝ) = ((7451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_943 : ((((452233766879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7451 < q → q < 7457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7457).mp (by decide +kernel))) hgap
  have hprev := s2L_942
  have hrat : ((452233766879 : ℚ) / 1000000000000) ≤ ((14132304653 : ℚ) / 31250000000) + (7457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233766879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132304653 : ℚ) / 31250000000) : ℚ) : ℝ) + ((7457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7457:ℚ)^(-2:ℤ) : ℝ) = ((7457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_944 : ((((113058446213 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7457 < q → q < 7459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7459).mp (by decide +kernel))) hgap
  have hprev := s2L_943
  have hrat : ((113058446213 : ℚ) / 250000000000) ≤ ((452233766879 : ℚ) / 1000000000000) + (7459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058446213 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233766879 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7459:ℚ)^(-2:ℤ) : ℝ) = ((7459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_945 : ((((452233802739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7459 < q → q < 7477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7477).mp (by decide +kernel))) hgap
  have hprev := s2L_944
  have hrat : ((452233802739 : ℚ) / 1000000000000) ≤ ((113058446213 : ℚ) / 250000000000) + (7477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233802739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058446213 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7477:ℚ)^(-2:ℤ) : ℝ) = ((7477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_946 : ((((452233820607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7481, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7477 < q → q < 7481 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7481).mp (by decide +kernel))) hgap
  have hprev := s2L_945
  have hrat : ((452233820607 : ℚ) / 1000000000000) ≤ ((452233802739 : ℚ) / 1000000000000) + (7481:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233820607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452233802739 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7481:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7481:ℚ)^(-2:ℤ) : ℝ) = ((7481:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_947 : ((((226116919223 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7481 < q → q < 7487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7487).mp (by decide +kernel))) hgap
  have hprev := s2L_946
  have hrat : ((226116919223 : ℚ) / 500000000000) ≤ ((452233820607 : ℚ) / 1000000000000) + (7487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116919223 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452233820607 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7487:ℚ)^(-2:ℤ) : ℝ) = ((7487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_948 : ((((113058464069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7487 < q → q < 7489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7489).mp (by decide +kernel))) hgap
  have hprev := s2L_947
  have hrat : ((113058464069 : ℚ) / 250000000000) ≤ ((226116919223 : ℚ) / 500000000000) + (7489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058464069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226116919223 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7489:ℚ)^(-2:ℤ) : ℝ) = ((7489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_949 : ((((226116937029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7489 < q → q < 7499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7499).mp (by decide +kernel))) hgap
  have hprev := s2L_948
  have hrat : ((226116937029 : ℚ) / 500000000000) ≤ ((113058464069 : ℚ) / 250000000000) + (7499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116937029 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058464069 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7499:ℚ)^(-2:ℤ) : ℝ) = ((7499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_950 : ((((226116945901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7507, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7499 < q → q < 7507 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7507).mp (by decide +kernel))) hgap
  have hprev := s2L_949
  have hrat : ((226116945901 : ℚ) / 500000000000) ≤ ((226116937029 : ℚ) / 500000000000) + (7507:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226116945901 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226116937029 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7507:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7507:ℚ)^(-2:ℤ) : ℝ) = ((7507:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_951 : ((((452233909499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7507 < q → q < 7517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7517).mp (by decide +kernel))) hgap
  have hprev := s2L_950
  have hrat : ((452233909499 : ℚ) / 1000000000000) ≤ ((226116945901 : ℚ) / 500000000000) + (7517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233909499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226116945901 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7517:ℚ)^(-2:ℤ) : ℝ) = ((7517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_952 : ((((883269389 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7517 < q → q < 7523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7523).mp (by decide +kernel))) hgap
  have hprev := s2L_951
  have hrat : ((883269389 : ℚ) / 1953125000) ≤ ((452233909499 : ℚ) / 1000000000000) + (7523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((883269389 : ℚ) / 1953125000) : ℚ) : ℝ) ≤ ((((452233909499 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7523:ℚ)^(-2:ℤ) : ℝ) = ((7523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_953 : ((((452233944809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7523 < q → q < 7529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7529).mp (by decide +kernel))) hgap
  have hprev := s2L_952
  have hrat : ((452233944809 : ℚ) / 1000000000000) ≤ ((883269389 : ℚ) / 1953125000) + (7529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233944809 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((883269389 : ℚ) / 1953125000) : ℚ) : ℝ) + ((7529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7529:ℚ)^(-2:ℤ) : ℝ) = ((7529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_954 : ((((113058490603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7529 < q → q < 7537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7537).mp (by decide +kernel))) hgap
  have hprev := s2L_953
  have hrat : ((113058490603 : ℚ) / 250000000000) ≤ ((452233944809 : ℚ) / 1000000000000) + (7537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058490603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452233944809 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7537:ℚ)^(-2:ℤ) : ℝ) = ((7537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_955 : ((((113058494999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7537 < q → q < 7541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7541).mp (by decide +kernel))) hgap
  have hprev := s2L_954
  have hrat : ((113058494999 : ℚ) / 250000000000) ≤ ((113058490603 : ℚ) / 250000000000) + (7541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058494999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113058490603 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7541:ℚ)^(-2:ℤ) : ℝ) = ((7541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_956 : ((((452233997553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7541 < q → q < 7547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7547).mp (by decide +kernel))) hgap
  have hprev := s2L_955
  have hrat : ((452233997553 : ℚ) / 1000000000000) ≤ ((113058494999 : ℚ) / 250000000000) + (7547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452233997553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058494999 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7547:ℚ)^(-2:ℤ) : ℝ) = ((7547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_957 : ((((4522340151 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7547 < q → q < 7549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7549).mp (by decide +kernel))) hgap
  have hprev := s2L_956
  have hrat : ((4522340151 : ℚ) / 10000000000) ≤ ((452233997553 : ℚ) / 1000000000000) + (7549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522340151 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452233997553 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7549:ℚ)^(-2:ℤ) : ℝ) = ((7549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_958 : ((((452234032601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7549 < q → q < 7559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7559).mp (by decide +kernel))) hgap
  have hprev := s2L_957
  have hrat : ((452234032601 : ℚ) / 1000000000000) ≤ ((4522340151 : ℚ) / 10000000000) + (7559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234032601 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522340151 : ℚ) / 10000000000) : ℚ) : ℝ) + ((7559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7559:ℚ)^(-2:ℤ) : ℝ) = ((7559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_959 : ((((452234050093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7561, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7559 < q → q < 7561 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7561).mp (by decide +kernel))) hgap
  have hprev := s2L_958
  have hrat : ((452234050093 : ℚ) / 1000000000000) ≤ ((452234032601 : ℚ) / 1000000000000) + (7561:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234050093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234032601 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7561:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7561:ℚ)^(-2:ℤ) : ℝ) = ((7561:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_960 : ((((452234067529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7561 < q → q < 7573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7573).mp (by decide +kernel))) hgap
  have hprev := s2L_959
  have hrat : ((452234067529 : ℚ) / 1000000000000) ≤ ((452234050093 : ℚ) / 1000000000000) + (7573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234067529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234050093 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7573:ℚ)^(-2:ℤ) : ℝ) = ((7573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_961 : ((((452234084947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7573 < q → q < 7577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7577).mp (by decide +kernel))) hgap
  have hprev := s2L_960
  have hrat : ((452234084947 : ℚ) / 1000000000000) ≤ ((452234067529 : ℚ) / 1000000000000) + (7577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234084947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234067529 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7577:ℚ)^(-2:ℤ) : ℝ) = ((7577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_962 : ((((452234102337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7577 < q → q < 7583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7583).mp (by decide +kernel))) hgap
  have hprev := s2L_961
  have hrat : ((452234102337 : ℚ) / 1000000000000) ≤ ((452234084947 : ℚ) / 1000000000000) + (7583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234102337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234084947 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7583:ℚ)^(-2:ℤ) : ℝ) = ((7583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_963 : ((((4522341197 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7589, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7583 < q → q < 7589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7589).mp (by decide +kernel))) hgap
  have hprev := s2L_962
  have hrat : ((4522341197 : ℚ) / 10000000000) ≤ ((452234102337 : ℚ) / 1000000000000) + (7589:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522341197 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((452234102337 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7589:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7589:ℚ)^(-2:ℤ) : ℝ) = ((7589:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_964 : ((((226117068527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7591, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7589 < q → q < 7591 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7591).mp (by decide +kernel))) hgap
  have hprev := s2L_963
  have hrat : ((226117068527 : ℚ) / 500000000000) ≤ ((4522341197 : ℚ) / 10000000000) + (7591:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117068527 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522341197 : ℚ) / 10000000000) : ℚ) : ℝ) + ((7591:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7591:ℚ)^(-2:ℤ) : ℝ) = ((7591:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_965 : ((((452234154353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7603, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7591 < q → q < 7603 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7603).mp (by decide +kernel))) hgap
  have hprev := s2L_964
  have hrat : ((452234154353 : ℚ) / 1000000000000) ≤ ((226117068527 : ℚ) / 500000000000) + (7603:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234154353 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117068527 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7603:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7603:ℚ)^(-2:ℤ) : ℝ) = ((7603:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_966 : ((((226117085817 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7603 < q → q < 7607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7607).mp (by decide +kernel))) hgap
  have hprev := s2L_965
  have hrat : ((226117085817 : ℚ) / 500000000000) ≤ ((452234154353 : ℚ) / 1000000000000) + (7607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117085817 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452234154353 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7607:ℚ)^(-2:ℤ) : ℝ) = ((7607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_967 : ((((452234188851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7607 < q → q < 7621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7621).mp (by decide +kernel))) hgap
  have hprev := s2L_966
  have hrat : ((452234188851 : ℚ) / 1000000000000) ≤ ((226117085817 : ℚ) / 500000000000) + (7621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234188851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117085817 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7621:ℚ)^(-2:ℤ) : ℝ) = ((7621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_968 : ((((452234205987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7621 < q → q < 7639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7639).mp (by decide +kernel))) hgap
  have hprev := s2L_967
  have hrat : ((452234205987 : ℚ) / 1000000000000) ≤ ((452234188851 : ℚ) / 1000000000000) + (7639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234205987 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234188851 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7639:ℚ)^(-2:ℤ) : ℝ) = ((7639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_969 : ((((90446844621 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7639 < q → q < 7643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7643).mp (by decide +kernel))) hgap
  have hprev := s2L_968
  have hrat : ((90446844621 : ℚ) / 200000000000) ≤ ((452234205987 : ℚ) / 1000000000000) + (7643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446844621 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452234205987 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7643:ℚ)^(-2:ℤ) : ℝ) = ((7643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_970 : ((((113058560049 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7643 < q → q < 7649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7649).mp (by decide +kernel))) hgap
  have hprev := s2L_969
  have hrat : ((113058560049 : ℚ) / 250000000000) ≤ ((90446844621 : ℚ) / 200000000000) + (7649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058560049 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90446844621 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7649:ℚ)^(-2:ℤ) : ℝ) = ((7649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_971 : ((((226117128599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7649 < q → q < 7669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7669).mp (by decide +kernel))) hgap
  have hprev := s2L_970
  have hrat : ((226117128599 : ℚ) / 500000000000) ≤ ((113058560049 : ℚ) / 250000000000) + (7669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117128599 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058560049 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7669:ℚ)^(-2:ℤ) : ℝ) = ((7669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_972 : ((((452234274183 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7673, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7669 < q → q < 7673 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7673).mp (by decide +kernel))) hgap
  have hprev := s2L_971
  have hrat : ((452234274183 : ℚ) / 1000000000000) ≤ ((226117128599 : ℚ) / 500000000000) + (7673:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234274183 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117128599 : ℚ) / 500000000000) : ℚ) : ℝ) + ((7673:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7673:ℚ)^(-2:ℤ) : ℝ) = ((7673:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_973 : ((((113058572783 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7673 < q → q < 7681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7681).mp (by decide +kernel))) hgap
  have hprev := s2L_972
  have hrat : ((113058572783 : ℚ) / 250000000000) ≤ ((452234274183 : ℚ) / 1000000000000) + (7681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058572783 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452234274183 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7681:ℚ)^(-2:ℤ) : ℝ) = ((7681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_974 : ((((90446861611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7681 < q → q < 7687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7687).mp (by decide +kernel))) hgap
  have hprev := s2L_973
  have hrat : ((90446861611 : ℚ) / 200000000000) ≤ ((113058572783 : ℚ) / 250000000000) + (7687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446861611 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113058572783 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7687:ℚ)^(-2:ℤ) : ℝ) = ((7687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_975 : ((((2826464531 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7687 < q → q < 7691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7691).mp (by decide +kernel))) hgap
  have hprev := s2L_974
  have hrat : ((2826464531 : ℚ) / 6250000000) ≤ ((90446861611 : ℚ) / 200000000000) + (7691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2826464531 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((90446861611 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7691:ℚ)^(-2:ℤ) : ℝ) = ((7691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_976 : ((((45223434183 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7691 < q → q < 7699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7699).mp (by decide +kernel))) hgap
  have hprev := s2L_975
  have hrat : ((45223434183 : ℚ) / 100000000000) ≤ ((2826464531 : ℚ) / 6250000000) + (7699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223434183 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((2826464531 : ℚ) / 6250000000) : ℚ) : ℝ) + ((7699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7699:ℚ)^(-2:ℤ) : ℝ) = ((7699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_977 : ((((452234358683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7699 < q → q < 7703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7703).mp (by decide +kernel))) hgap
  have hprev := s2L_976
  have hrat : ((452234358683 : ℚ) / 1000000000000) ≤ ((45223434183 : ℚ) / 100000000000) + (7703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234358683 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223434183 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7703:ℚ)^(-2:ℤ) : ℝ) = ((7703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_978 : ((((18089375019 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7703 < q → q < 7717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7717).mp (by decide +kernel))) hgap
  have hprev := s2L_977
  have hrat : ((18089375019 : ℚ) / 40000000000) ≤ ((452234358683 : ℚ) / 1000000000000) + (7717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089375019 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452234358683 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7717:ℚ)^(-2:ℤ) : ℝ) = ((7717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_979 : ((((5652929903 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7717 < q → q < 7723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7723).mp (by decide +kernel))) hgap
  have hprev := s2L_978
  have hrat : ((5652929903 : ℚ) / 12500000000) ≤ ((18089375019 : ℚ) / 40000000000) + (7723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((5652929903 : ℚ) / 12500000000) : ℚ) : ℝ) ≤ ((((18089375019 : ℚ) / 40000000000) : ℚ) : ℝ) + ((7723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7723:ℚ)^(-2:ℤ) : ℝ) = ((7723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_980 : ((((113058602247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7727, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7723 < q → q < 7727 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7727).mp (by decide +kernel))) hgap
  have hprev := s2L_979
  have hrat : ((113058602247 : ℚ) / 250000000000) ≤ ((5652929903 : ℚ) / 12500000000) + (7727:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058602247 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((5652929903 : ℚ) / 12500000000) : ℚ) : ℝ) + ((7727:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7727:ℚ)^(-2:ℤ) : ℝ) = ((7727:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_981 : ((((113058606419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7727 < q → q < 7741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7741).mp (by decide +kernel))) hgap
  have hprev := s2L_980
  have hrat : ((113058606419 : ℚ) / 250000000000) ≤ ((113058602247 : ℚ) / 250000000000) + (7741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058606419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113058602247 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7741:ℚ)^(-2:ℤ) : ℝ) = ((7741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_982 : ((((56529305289 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7741 < q → q < 7753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7753).mp (by decide +kernel))) hgap
  have hprev := s2L_981
  have hrat : ((56529305289 : ℚ) / 125000000000) ≤ ((113058606419 : ℚ) / 250000000000) + (7753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529305289 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113058606419 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7753:ℚ)^(-2:ℤ) : ℝ) = ((7753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_983 : ((((452234458931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7753 < q → q < 7757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7757).mp (by decide +kernel))) hgap
  have hprev := s2L_982
  have hrat : ((452234458931 : ℚ) / 1000000000000) ≤ ((56529305289 : ℚ) / 125000000000) + (7757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234458931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529305289 : ℚ) / 125000000000) : ℚ) : ℝ) + ((7757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7757:ℚ)^(-2:ℤ) : ℝ) = ((7757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_984 : ((((452234475541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7759, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7757 < q → q < 7759 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7759).mp (by decide +kernel))) hgap
  have hprev := s2L_983
  have hrat : ((452234475541 : ℚ) / 1000000000000) ≤ ((452234458931 : ℚ) / 1000000000000) + (7759:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234475541 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234458931 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7759:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7759:ℚ)^(-2:ℤ) : ℝ) = ((7759:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_985 : ((((56529311503 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7759 < q → q < 7789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7789).mp (by decide +kernel))) hgap
  have hprev := s2L_984
  have hrat : ((56529311503 : ℚ) / 125000000000) ≤ ((452234475541 : ℚ) / 1000000000000) + (7789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529311503 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452234475541 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7789:ℚ)^(-2:ℤ) : ℝ) = ((7789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_986 : ((((45223450849 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7793, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7789 < q → q < 7793 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7793).mp (by decide +kernel))) hgap
  have hprev := s2L_985
  have hrat : ((45223450849 : ℚ) / 100000000000) ≤ ((56529311503 : ℚ) / 125000000000) + (7793:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223450849 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((56529311503 : ℚ) / 125000000000) : ℚ) : ℝ) + ((7793:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7793:ℚ)^(-2:ℤ) : ℝ) = ((7793:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_987 : ((((90446904971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7793 < q → q < 7817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7817).mp (by decide +kernel))) hgap
  have hprev := s2L_986
  have hrat : ((90446904971 : ℚ) / 200000000000) ≤ ((45223450849 : ℚ) / 100000000000) + (7817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446904971 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((45223450849 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7817:ℚ)^(-2:ℤ) : ℝ) = ((7817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_988 : ((((90446908239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7817 < q → q < 7823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7823).mp (by decide +kernel))) hgap
  have hprev := s2L_987
  have hrat : ((90446908239 : ℚ) / 200000000000) ≤ ((90446904971 : ℚ) / 200000000000) + (7823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446908239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90446904971 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7823:ℚ)^(-2:ℤ) : ℝ) = ((7823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_989 : ((((45223455751 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7823 < q → q < 7829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7829).mp (by decide +kernel))) hgap
  have hprev := s2L_988
  have hrat : ((45223455751 : ℚ) / 100000000000) ≤ ((90446908239 : ℚ) / 200000000000) + (7829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223455751 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90446908239 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7829:ℚ)^(-2:ℤ) : ℝ) = ((7829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_990 : ((((18089382951 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7829 < q → q < 7841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7841).mp (by decide +kernel))) hgap
  have hprev := s2L_989
  have hrat : ((18089382951 : ℚ) / 40000000000) ≤ ((45223455751 : ℚ) / 100000000000) + (7841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089382951 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((45223455751 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7841:ℚ)^(-2:ℤ) : ℝ) = ((7841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_991 : ((((45223458999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7841 < q → q < 7853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7853).mp (by decide +kernel))) hgap
  have hprev := s2L_990
  have hrat : ((45223458999 : ℚ) / 100000000000) ≤ ((18089382951 : ℚ) / 40000000000) + (7853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223458999 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((18089382951 : ℚ) / 40000000000) : ℚ) : ℝ) + ((7853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7853:ℚ)^(-2:ℤ) : ℝ) = ((7853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_992 : ((((452234606147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7853 < q → q < 7867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7867).mp (by decide +kernel))) hgap
  have hprev := s2L_991
  have hrat : ((452234606147 : ℚ) / 1000000000000) ≤ ((45223458999 : ℚ) / 100000000000) + (7867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234606147 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223458999 : ℚ) / 100000000000) : ℚ) : ℝ) + ((7867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7867:ℚ)^(-2:ℤ) : ℝ) = ((7867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_993 : ((((11305865557 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7873, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7867 < q → q < 7873 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7873).mp (by decide +kernel))) hgap
  have hprev := s2L_992
  have hrat : ((11305865557 : ℚ) / 25000000000) ≤ ((452234606147 : ℚ) / 1000000000000) + (7873:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305865557 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452234606147 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7873:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7873:ℚ)^(-2:ℤ) : ℝ) = ((7873:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_994 : ((((113058659599 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7877, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7873 < q → q < 7877 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7877).mp (by decide +kernel))) hgap
  have hprev := s2L_993
  have hrat : ((113058659599 : ℚ) / 250000000000) ≤ ((11305865557 : ℚ) / 25000000000) + (7877:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058659599 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11305865557 : ℚ) / 25000000000) : ℚ) : ℝ) + ((7877:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7877:ℚ)^(-2:ℤ) : ℝ) = ((7877:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_995 : ((((56529331813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7879, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7877 < q → q < 7879 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7879).mp (by decide +kernel))) hgap
  have hprev := s2L_994
  have hrat : ((56529331813 : ℚ) / 125000000000) ≤ ((113058659599 : ℚ) / 250000000000) + (7879:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529331813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113058659599 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7879:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7879:ℚ)^(-2:ℤ) : ℝ) = ((7879:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_996 : ((((113058667649 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7879 < q → q < 7883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7883).mp (by decide +kernel))) hgap
  have hprev := s2L_995
  have hrat : ((113058667649 : ℚ) / 250000000000) ≤ ((56529331813 : ℚ) / 125000000000) + (7883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058667649 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56529331813 : ℚ) / 125000000000) : ℚ) : ℝ) + ((7883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7883:ℚ)^(-2:ℤ) : ℝ) = ((7883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_997 : ((((90446937323 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7883 < q → q < 7901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7901).mp (by decide +kernel))) hgap
  have hprev := s2L_996
  have hrat : ((90446937323 : ℚ) / 200000000000) ≤ ((113058667649 : ℚ) / 250000000000) + (7901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446937323 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113058667649 : ℚ) / 250000000000) : ℚ) : ℝ) + ((7901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7901:ℚ)^(-2:ℤ) : ℝ) = ((7901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_998 : ((((452234702609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7901 < q → q < 7907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7907).mp (by decide +kernel))) hgap
  have hprev := s2L_997
  have hrat : ((452234702609 : ℚ) / 1000000000000) ≤ ((90446937323 : ℚ) / 200000000000) + (7907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234702609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446937323 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7907:ℚ)^(-2:ℤ) : ℝ) = ((7907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_999 : ((((90446943711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7907 < q → q < 7919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7919).mp (by decide +kernel))) hgap
  have hprev := s2L_998
  have hrat : ((90446943711 : ℚ) / 200000000000) ≤ ((452234702609 : ℚ) / 1000000000000) + (7919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90446943711 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452234702609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7919:ℚ)^(-2:ℤ) : ℝ) = ((7919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1000 : ((((452234734469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7919 < q → q < 7927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7927).mp (by decide +kernel))) hgap
  have hprev := s2L_999
  have hrat : ((452234734469 : ℚ) / 1000000000000) ≤ ((90446943711 : ℚ) / 200000000000) + (7927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234734469 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90446943711 : ℚ) / 200000000000) : ℚ) : ℝ) + ((7927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7927:ℚ)^(-2:ℤ) : ℝ) = ((7927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1001 : ((((452234750359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7927 < q → q < 7933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7933).mp (by decide +kernel))) hgap
  have hprev := s2L_1000
  have hrat : ((452234750359 : ℚ) / 1000000000000) ≤ ((452234734469 : ℚ) / 1000000000000) + (7933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234750359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234734469 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7933:ℚ)^(-2:ℤ) : ℝ) = ((7933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1002 : ((((452234766233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7933 < q → q < 7937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7937).mp (by decide +kernel))) hgap
  have hprev := s2L_1001
  have hrat : ((452234766233 : ℚ) / 1000000000000) ≤ ((452234750359 : ℚ) / 1000000000000) + (7937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234766233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234750359 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7937:ℚ)^(-2:ℤ) : ℝ) = ((7937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1003 : ((((452234782059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7937 < q → q < 7949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7949).mp (by decide +kernel))) hgap
  have hprev := s2L_1002
  have hrat : ((452234782059 : ℚ) / 1000000000000) ≤ ((452234766233 : ℚ) / 1000000000000) + (7949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234782059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234766233 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7949:ℚ)^(-2:ℤ) : ℝ) = ((7949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1004 : ((((452234797877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7949 < q → q < 7951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7951).mp (by decide +kernel))) hgap
  have hprev := s2L_1003
  have hrat : ((452234797877 : ℚ) / 1000000000000) ≤ ((452234782059 : ℚ) / 1000000000000) + (7951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234797877 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234782059 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7951:ℚ)^(-2:ℤ) : ℝ) = ((7951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1005 : ((((452234813647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7951 < q → q < 7963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7963).mp (by decide +kernel))) hgap
  have hprev := s2L_1004
  have hrat : ((452234813647 : ℚ) / 1000000000000) ≤ ((452234797877 : ℚ) / 1000000000000) + (7963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234813647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234797877 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7963:ℚ)^(-2:ℤ) : ℝ) = ((7963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1006 : ((((452234829299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 7993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7963 < q → q < 7993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 7993).mp (by decide +kernel))) hgap
  have hprev := s2L_1005
  have hrat : ((452234829299 : ℚ) / 1000000000000) ≤ ((452234813647 : ℚ) / 1000000000000) + (7993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234829299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234813647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((7993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((7993:ℚ)^(-2:ℤ) : ℝ) = ((7993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1007 : ((((56529355611 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 7993 < q → q < 8009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8009).mp (by decide +kernel))) hgap
  have hprev := s2L_1006
  have hrat : ((56529355611 : ℚ) / 125000000000) ≤ ((452234829299 : ℚ) / 1000000000000) + (8009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529355611 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452234829299 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8009:ℚ)^(-2:ℤ) : ℝ) = ((8009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1008 : ((((45223486047 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8009 < q → q < 8011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8011).mp (by decide +kernel))) hgap
  have hprev := s2L_1007
  have hrat : ((45223486047 : ℚ) / 100000000000) ≤ ((56529355611 : ℚ) / 125000000000) + (8011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223486047 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((56529355611 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8011:ℚ)^(-2:ℤ) : ℝ) = ((8011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1009 : ((((113058719007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8017, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8011 < q → q < 8017 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8017).mp (by decide +kernel))) hgap
  have hprev := s2L_1008
  have hrat : ((113058719007 : ℚ) / 250000000000) ≤ ((45223486047 : ℚ) / 100000000000) + (8017:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058719007 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45223486047 : ℚ) / 100000000000) : ℚ) : ℝ) + ((8017:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8017:ℚ)^(-2:ℤ) : ℝ) = ((8017:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1010 : ((((452234891501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8017 < q → q < 8039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8039).mp (by decide +kernel))) hgap
  have hprev := s2L_1009
  have hrat : ((452234891501 : ℚ) / 1000000000000) ≤ ((113058719007 : ℚ) / 250000000000) + (8039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234891501 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058719007 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8039:ℚ)^(-2:ℤ) : ℝ) = ((8039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1011 : ((((452234906921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8053, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8039 < q → q < 8053 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8053).mp (by decide +kernel))) hgap
  have hprev := s2L_1010
  have hrat : ((452234906921 : ℚ) / 1000000000000) ≤ ((452234891501 : ℚ) / 1000000000000) + (8053:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234906921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234891501 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8053:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8053:ℚ)^(-2:ℤ) : ℝ) = ((8053:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1012 : ((((226117461159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8053 < q → q < 8059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8059).mp (by decide +kernel))) hgap
  have hprev := s2L_1011
  have hrat : ((226117461159 : ℚ) / 500000000000) ≤ ((452234906921 : ℚ) / 1000000000000) + (8059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117461159 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452234906921 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8059:ℚ)^(-2:ℤ) : ℝ) = ((8059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1013 : ((((113058734419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8059 < q → q < 8069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8069).mp (by decide +kernel))) hgap
  have hprev := s2L_1012
  have hrat : ((113058734419 : ℚ) / 250000000000) ≤ ((226117461159 : ℚ) / 500000000000) + (8069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058734419 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226117461159 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8069:ℚ)^(-2:ℤ) : ℝ) = ((8069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1014 : ((((452234952989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8081, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8069 < q → q < 8081 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8081).mp (by decide +kernel))) hgap
  have hprev := s2L_1013
  have hrat : ((452234952989 : ℚ) / 1000000000000) ≤ ((113058734419 : ℚ) / 250000000000) + (8081:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234952989 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058734419 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8081:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8081:ℚ)^(-2:ℤ) : ℝ) = ((8081:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1015 : ((((452234968279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8081 < q → q < 8087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8087).mp (by decide +kernel))) hgap
  have hprev := s2L_1014
  have hrat : ((452234968279 : ℚ) / 1000000000000) ≤ ((452234952989 : ℚ) / 1000000000000) + (8087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234968279 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452234952989 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8087:ℚ)^(-2:ℤ) : ℝ) = ((8087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1016 : ((((226117491781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8089, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8087 < q → q < 8089 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8089).mp (by decide +kernel))) hgap
  have hprev := s2L_1015
  have hrat : ((226117491781 : ℚ) / 500000000000) ≤ ((452234968279 : ℚ) / 1000000000000) + (8089:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117491781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452234968279 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8089:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8089:ℚ)^(-2:ℤ) : ℝ) = ((8089:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1017 : ((((452234998829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8089 < q → q < 8093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8093).mp (by decide +kernel))) hgap
  have hprev := s2L_1016
  have hrat : ((452234998829 : ℚ) / 1000000000000) ≤ ((226117491781 : ℚ) / 500000000000) + (8093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452234998829 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117491781 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8093:ℚ)^(-2:ℤ) : ℝ) = ((8093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1018 : ((((226117507033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8093 < q → q < 8101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8101).mp (by decide +kernel))) hgap
  have hprev := s2L_1017
  have hrat : ((226117507033 : ℚ) / 500000000000) ≤ ((452234998829 : ℚ) / 1000000000000) + (8101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117507033 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452234998829 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8101:ℚ)^(-2:ℤ) : ℝ) = ((8101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1019 : ((((226117514633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8101 < q → q < 8111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8111).mp (by decide +kernel))) hgap
  have hprev := s2L_1018
  have hrat : ((226117514633 : ℚ) / 500000000000) ≤ ((226117507033 : ℚ) / 500000000000) + (8111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117514633 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226117507033 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8111:ℚ)^(-2:ℤ) : ℝ) = ((8111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1020 : ((((452235044443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8111 < q → q < 8117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8117).mp (by decide +kernel))) hgap
  have hprev := s2L_1019
  have hrat : ((452235044443 : ℚ) / 1000000000000) ≤ ((226117514633 : ℚ) / 500000000000) + (8117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235044443 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117514633 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8117:ℚ)^(-2:ℤ) : ℝ) = ((8117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1021 : ((((226117529799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8123, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8117 < q → q < 8123 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8123).mp (by decide +kernel))) hgap
  have hprev := s2L_1020
  have hrat : ((226117529799 : ℚ) / 500000000000) ≤ ((452235044443 : ℚ) / 1000000000000) + (8123:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117529799 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452235044443 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8123:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8123:ℚ)^(-2:ℤ) : ℝ) = ((8123:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1022 : ((((56529384333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8123 < q → q < 8147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8147).mp (by decide +kernel))) hgap
  have hprev := s2L_1021
  have hrat : ((56529384333 : ℚ) / 125000000000) ≤ ((226117529799 : ℚ) / 500000000000) + (8147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529384333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226117529799 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8147:ℚ)^(-2:ℤ) : ℝ) = ((8147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1023 : ((((226117544839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8147 < q → q < 8161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8161).mp (by decide +kernel))) hgap
  have hprev := s2L_1022
  have hrat : ((226117544839 : ℚ) / 500000000000) ≤ ((56529384333 : ℚ) / 125000000000) + (8161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117544839 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529384333 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8161:ℚ)^(-2:ℤ) : ℝ) = ((8161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1024 : ((((45223510467 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8167, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8161 < q → q < 8167 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8167).mp (by decide +kernel))) hgap
  have hprev := s2L_1023
  have hrat : ((45223510467 : ℚ) / 100000000000) ≤ ((226117544839 : ℚ) / 500000000000) + (8167:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223510467 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226117544839 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8167:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8167:ℚ)^(-2:ℤ) : ℝ) = ((8167:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1025 : ((((452235119647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8167 < q → q < 8171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8171).mp (by decide +kernel))) hgap
  have hprev := s2L_1024
  have hrat : ((452235119647 : ℚ) / 1000000000000) ≤ ((45223510467 : ℚ) / 100000000000) + (8171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235119647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223510467 : ℚ) / 100000000000) : ℚ) : ℝ) + ((8171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8171:ℚ)^(-2:ℤ) : ℝ) = ((8171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1026 : ((((90447026919 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8179, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8171 < q → q < 8179 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8179).mp (by decide +kernel))) hgap
  have hprev := s2L_1025
  have hrat : ((90447026919 : ℚ) / 200000000000) ≤ ((452235119647 : ℚ) / 1000000000000) + (8179:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447026919 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452235119647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8179:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8179:ℚ)^(-2:ℤ) : ℝ) = ((8179:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1027 : ((((452235149499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8191, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8179 < q → q < 8191 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8191).mp (by decide +kernel))) hgap
  have hprev := s2L_1026
  have hrat : ((452235149499 : ℚ) / 1000000000000) ≤ ((90447026919 : ℚ) / 200000000000) + (8191:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235149499 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447026919 : ℚ) / 200000000000) : ℚ) : ℝ) + ((8191:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8191:ℚ)^(-2:ℤ) : ℝ) = ((8191:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1028 : ((((226117582169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8191 < q → q < 8209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8209).mp (by decide +kernel))) hgap
  have hprev := s2L_1027
  have hrat : ((226117582169 : ℚ) / 500000000000) ≤ ((452235149499 : ℚ) / 1000000000000) + (8209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117582169 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452235149499 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8209:ℚ)^(-2:ℤ) : ℝ) = ((8209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1029 : ((((452235179141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8209 < q → q < 8219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8219).mp (by decide +kernel))) hgap
  have hprev := s2L_1028
  have hrat : ((452235179141 : ℚ) / 1000000000000) ≤ ((226117582169 : ℚ) / 500000000000) + (8219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235179141 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117582169 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8219:ℚ)^(-2:ℤ) : ℝ) = ((8219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1030 : ((((452235193937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8219 < q → q < 8221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8221).mp (by decide +kernel))) hgap
  have hprev := s2L_1029
  have hrat : ((452235193937 : ℚ) / 1000000000000) ≤ ((452235179141 : ℚ) / 1000000000000) + (8221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235193937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235179141 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8221:ℚ)^(-2:ℤ) : ℝ) = ((8221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1031 : ((((452235208697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8231, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8221 < q → q < 8231 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8231).mp (by decide +kernel))) hgap
  have hprev := s2L_1030
  have hrat : ((452235208697 : ℚ) / 1000000000000) ≤ ((452235193937 : ℚ) / 1000000000000) + (8231:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235208697 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235193937 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8231:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8231:ℚ)^(-2:ℤ) : ℝ) = ((8231:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1032 : ((((9044704469 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8233, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8231 < q → q < 8233 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8233).mp (by decide +kernel))) hgap
  have hprev := s2L_1031
  have hrat : ((9044704469 : ℚ) / 20000000000) ≤ ((452235208697 : ℚ) / 1000000000000) + (8233:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044704469 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452235208697 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8233:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8233:ℚ)^(-2:ℤ) : ℝ) = ((8233:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1033 : ((((113058809547 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8237, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8233 < q → q < 8237 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8237).mp (by decide +kernel))) hgap
  have hprev := s2L_1032
  have hrat : ((113058809547 : ℚ) / 250000000000) ≤ ((9044704469 : ℚ) / 20000000000) + (8237:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058809547 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9044704469 : ℚ) / 20000000000) : ℚ) : ℝ) + ((8237:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8237:ℚ)^(-2:ℤ) : ℝ) = ((8237:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1034 : ((((90447050581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8237 < q → q < 8243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8243).mp (by decide +kernel))) hgap
  have hprev := s2L_1033
  have hrat : ((90447050581 : ℚ) / 200000000000) ≤ ((113058809547 : ℚ) / 250000000000) + (8243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447050581 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113058809547 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8243:ℚ)^(-2:ℤ) : ℝ) = ((8243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1035 : ((((452235267551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8243 < q → q < 8263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8263).mp (by decide +kernel))) hgap
  have hprev := s2L_1034
  have hrat : ((452235267551 : ℚ) / 1000000000000) ≤ ((90447050581 : ℚ) / 200000000000) + (8263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235267551 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447050581 : ℚ) / 200000000000) : ℚ) : ℝ) + ((8263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8263:ℚ)^(-2:ℤ) : ℝ) = ((8263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1036 : ((((18089411287 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8263 < q → q < 8269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8269).mp (by decide +kernel))) hgap
  have hprev := s2L_1035
  have hrat : ((18089411287 : ℚ) / 40000000000) ≤ ((452235267551 : ℚ) / 1000000000000) + (8269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089411287 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452235267551 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8269:ℚ)^(-2:ℤ) : ℝ) = ((8269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1037 : ((((90447059357 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8269 < q → q < 8273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8273).mp (by decide +kernel))) hgap
  have hprev := s2L_1036
  have hrat : ((90447059357 : ℚ) / 200000000000) ≤ ((18089411287 : ℚ) / 40000000000) + (8273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447059357 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089411287 : ℚ) / 40000000000) : ℚ) : ℝ) + ((8273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8273:ℚ)^(-2:ℤ) : ℝ) = ((8273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1038 : ((((226117655673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8273 < q → q < 8287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8287).mp (by decide +kernel))) hgap
  have hprev := s2L_1037
  have hrat : ((226117655673 : ℚ) / 500000000000) ≤ ((90447059357 : ℚ) / 200000000000) + (8287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117655673 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447059357 : ℚ) / 200000000000) : ℚ) : ℝ) + ((8287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8287:ℚ)^(-2:ℤ) : ℝ) = ((8287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1039 : ((((452235325893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8287 < q → q < 8291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8291).mp (by decide +kernel))) hgap
  have hprev := s2L_1038
  have hrat : ((452235325893 : ℚ) / 1000000000000) ≤ ((226117655673 : ℚ) / 500000000000) + (8291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235325893 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117655673 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8291:ℚ)^(-2:ℤ) : ℝ) = ((8291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1040 : ((((452235340433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8291 < q → q < 8293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8293).mp (by decide +kernel))) hgap
  have hprev := s2L_1039
  have hrat : ((452235340433 : ℚ) / 1000000000000) ≤ ((452235325893 : ℚ) / 1000000000000) + (8293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235340433 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235325893 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8293:ℚ)^(-2:ℤ) : ℝ) = ((8293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1041 : ((((452235354959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8293 < q → q < 8297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8297).mp (by decide +kernel))) hgap
  have hprev := s2L_1040
  have hrat : ((452235354959 : ℚ) / 1000000000000) ≤ ((452235340433 : ℚ) / 1000000000000) + (8297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235354959 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235340433 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8297:ℚ)^(-2:ℤ) : ℝ) = ((8297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1042 : ((((113058842359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8297 < q → q < 8311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8311).mp (by decide +kernel))) hgap
  have hprev := s2L_1041
  have hrat : ((113058842359 : ℚ) / 250000000000) ≤ ((452235354959 : ℚ) / 1000000000000) + (8311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058842359 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452235354959 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8311:ℚ)^(-2:ℤ) : ℝ) = ((8311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1043 : ((((113058845973 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8311 < q → q < 8317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8317).mp (by decide +kernel))) hgap
  have hprev := s2L_1042
  have hrat : ((113058845973 : ℚ) / 250000000000) ≤ ((113058842359 : ℚ) / 250000000000) + (8317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058845973 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113058842359 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8317:ℚ)^(-2:ℤ) : ℝ) = ((8317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1044 : ((((226117699153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8317 < q → q < 8329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8329).mp (by decide +kernel))) hgap
  have hprev := s2L_1043
  have hrat : ((226117699153 : ℚ) / 500000000000) ≤ ((113058845973 : ℚ) / 250000000000) + (8329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117699153 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058845973 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8329:ℚ)^(-2:ℤ) : ℝ) = ((8329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1045 : ((((226117706319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8329 < q → q < 8353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8353).mp (by decide +kernel))) hgap
  have hprev := s2L_1044
  have hrat : ((226117706319 : ℚ) / 500000000000) ≤ ((226117699153 : ℚ) / 500000000000) + (8353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117706319 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226117699153 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8353:ℚ)^(-2:ℤ) : ℝ) = ((8353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1046 : ((((56529428367 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8363, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8353 < q → q < 8363 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8363).mp (by decide +kernel))) hgap
  have hprev := s2L_1045
  have hrat : ((56529428367 : ℚ) / 125000000000) ≤ ((226117706319 : ℚ) / 500000000000) + (8363:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529428367 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226117706319 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8363:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8363:ℚ)^(-2:ℤ) : ℝ) = ((8363:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1047 : ((((452235441213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8363 < q → q < 8369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8369).mp (by decide +kernel))) hgap
  have hprev := s2L_1046
  have hrat : ((452235441213 : ℚ) / 1000000000000) ≤ ((56529428367 : ℚ) / 125000000000) + (8369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235441213 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529428367 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8369:ℚ)^(-2:ℤ) : ℝ) = ((8369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1048 : ((((452235455463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8369 < q → q < 8377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8377).mp (by decide +kernel))) hgap
  have hprev := s2L_1047
  have hrat : ((452235455463 : ℚ) / 1000000000000) ≤ ((452235441213 : ℚ) / 1000000000000) + (8377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235455463 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235441213 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8377:ℚ)^(-2:ℤ) : ℝ) = ((8377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1049 : ((((452235469679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8387, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8377 < q → q < 8387 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8387).mp (by decide +kernel))) hgap
  have hprev := s2L_1048
  have hrat : ((452235469679 : ℚ) / 1000000000000) ≤ ((452235455463 : ℚ) / 1000000000000) + (8387:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235469679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235455463 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8387:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8387:ℚ)^(-2:ℤ) : ℝ) = ((8387:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1050 : ((((28264717743 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8389, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8387 < q → q < 8389 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8389).mp (by decide +kernel))) hgap
  have hprev := s2L_1049
  have hrat : ((28264717743 : ℚ) / 62500000000) ≤ ((452235469679 : ℚ) / 1000000000000) + (8389:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264717743 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452235469679 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8389:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8389:ℚ)^(-2:ℤ) : ℝ) = ((8389:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1051 : ((((113058874499 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8389 < q → q < 8419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8419).mp (by decide +kernel))) hgap
  have hprev := s2L_1050
  have hrat : ((113058874499 : ℚ) / 250000000000) ≤ ((28264717743 : ℚ) / 62500000000) + (8419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058874499 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28264717743 : ℚ) / 62500000000) : ℚ) : ℝ) + ((8419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8419:ℚ)^(-2:ℤ) : ℝ) = ((8419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1052 : ((((452235512091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8419 < q → q < 8423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8423).mp (by decide +kernel))) hgap
  have hprev := s2L_1051
  have hrat : ((452235512091 : ℚ) / 1000000000000) ≤ ((113058874499 : ℚ) / 250000000000) + (8423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235512091 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058874499 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8423:ℚ)^(-2:ℤ) : ℝ) = ((8423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1053 : ((((90447105233 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8423 < q → q < 8429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8429).mp (by decide +kernel))) hgap
  have hprev := s2L_1052
  have hrat : ((90447105233 : ℚ) / 200000000000) ≤ ((452235512091 : ℚ) / 1000000000000) + (8429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447105233 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452235512091 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8429:ℚ)^(-2:ℤ) : ℝ) = ((8429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1054 : ((((452235540233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8429 < q → q < 8431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8431).mp (by decide +kernel))) hgap
  have hprev := s2L_1053
  have hrat : ((452235540233 : ℚ) / 1000000000000) ≤ ((90447105233 : ℚ) / 200000000000) + (8431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235540233 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447105233 : ℚ) / 200000000000) : ℚ) : ℝ) + ((8431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8431:ℚ)^(-2:ℤ) : ℝ) = ((8431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1055 : ((((452235554261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8431 < q → q < 8443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8443).mp (by decide +kernel))) hgap
  have hprev := s2L_1054
  have hrat : ((452235554261 : ℚ) / 1000000000000) ≤ ((452235540233 : ℚ) / 1000000000000) + (8443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235554261 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235540233 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8443:ℚ)^(-2:ℤ) : ℝ) = ((8443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1056 : ((((113058892069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8443 < q → q < 8447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8447).mp (by decide +kernel))) hgap
  have hprev := s2L_1055
  have hrat : ((113058892069 : ℚ) / 250000000000) ≤ ((452235554261 : ℚ) / 1000000000000) + (8447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058892069 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452235554261 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8447:ℚ)^(-2:ℤ) : ℝ) = ((8447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1057 : ((((113058895561 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8447 < q → q < 8461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8461).mp (by decide +kernel))) hgap
  have hprev := s2L_1056
  have hrat : ((113058895561 : ℚ) / 250000000000) ≤ ((113058892069 : ℚ) / 250000000000) + (8461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058895561 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113058892069 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8461:ℚ)^(-2:ℤ) : ℝ) = ((8461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1058 : ((((14132362381 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8461 < q → q < 8467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8467).mp (by decide +kernel))) hgap
  have hprev := s2L_1057
  have hrat : ((14132362381 : ℚ) / 31250000000) ≤ ((113058895561 : ℚ) / 250000000000) + (8467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132362381 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113058895561 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8467:ℚ)^(-2:ℤ) : ℝ) = ((8467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1059 : ((((452235610029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8467 < q → q < 8501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8501).mp (by decide +kernel))) hgap
  have hprev := s2L_1058
  have hrat : ((452235610029 : ℚ) / 1000000000000) ≤ ((14132362381 : ℚ) / 31250000000) + (8501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235610029 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132362381 : ℚ) / 31250000000) : ℚ) : ℝ) + ((8501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8501:ℚ)^(-2:ℤ) : ℝ) = ((8501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1060 : ((((452235623827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8501 < q → q < 8513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8513).mp (by decide +kernel))) hgap
  have hprev := s2L_1059
  have hrat : ((452235623827 : ℚ) / 1000000000000) ≤ ((452235610029 : ℚ) / 1000000000000) + (8513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235623827 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235610029 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8513:ℚ)^(-2:ℤ) : ℝ) = ((8513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1061 : ((((452235637599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8513 < q → q < 8521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8521).mp (by decide +kernel))) hgap
  have hprev := s2L_1060
  have hrat : ((452235637599 : ℚ) / 1000000000000) ≤ ((452235623827 : ℚ) / 1000000000000) + (8521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235637599 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235623827 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8521:ℚ)^(-2:ℤ) : ℝ) = ((8521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1062 : ((((56529456419 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8521 < q → q < 8527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8527).mp (by decide +kernel))) hgap
  have hprev := s2L_1061
  have hrat : ((56529456419 : ℚ) / 125000000000) ≤ ((452235637599 : ℚ) / 1000000000000) + (8527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529456419 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452235637599 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8527:ℚ)^(-2:ℤ) : ℝ) = ((8527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1063 : ((((452235665073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8537, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8527 < q → q < 8537 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8537).mp (by decide +kernel))) hgap
  have hprev := s2L_1062
  have hrat : ((452235665073 : ℚ) / 1000000000000) ≤ ((56529456419 : ℚ) / 125000000000) + (8537:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235665073 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529456419 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8537:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8537:ℚ)^(-2:ℤ) : ℝ) = ((8537:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1064 : ((((452235678787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8537 < q → q < 8539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8539).mp (by decide +kernel))) hgap
  have hprev := s2L_1063
  have hrat : ((452235678787 : ℚ) / 1000000000000) ≤ ((452235665073 : ℚ) / 1000000000000) + (8539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235678787 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235665073 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8539:ℚ)^(-2:ℤ) : ℝ) = ((8539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1065 : ((((56529461561 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8543, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8539 < q → q < 8543 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8543).mp (by decide +kernel))) hgap
  have hprev := s2L_1064
  have hrat : ((56529461561 : ℚ) / 125000000000) ≤ ((452235678787 : ℚ) / 1000000000000) + (8543:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529461561 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452235678787 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8543:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8543:ℚ)^(-2:ℤ) : ℝ) = ((8543:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1066 : ((((3617885649 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8563, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8543 < q → q < 8563 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8563).mp (by decide +kernel))) hgap
  have hprev := s2L_1065
  have hrat : ((3617885649 : ℚ) / 8000000000) ≤ ((56529461561 : ℚ) / 125000000000) + (8563:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3617885649 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((56529461561 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8563:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8563:ℚ)^(-2:ℤ) : ℝ) = ((8563:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1067 : ((((452235719731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8573, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8563 < q → q < 8573 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8573).mp (by decide +kernel))) hgap
  have hprev := s2L_1066
  have hrat : ((452235719731 : ℚ) / 1000000000000) ≤ ((3617885649 : ℚ) / 8000000000) + (8573:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235719731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3617885649 : ℚ) / 8000000000) : ℚ) : ℝ) + ((8573:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8573:ℚ)^(-2:ℤ) : ℝ) = ((8573:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1068 : ((((452235733311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8581, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8573 < q → q < 8581 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8581).mp (by decide +kernel))) hgap
  have hprev := s2L_1067
  have hrat : ((452235733311 : ℚ) / 1000000000000) ≤ ((452235719731 : ℚ) / 1000000000000) + (8581:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235733311 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235719731 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8581:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8581:ℚ)^(-2:ℤ) : ℝ) = ((8581:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1069 : ((((452235746841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8581 < q → q < 8597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8597).mp (by decide +kernel))) hgap
  have hprev := s2L_1068
  have hrat : ((452235746841 : ℚ) / 1000000000000) ≤ ((452235733311 : ℚ) / 1000000000000) + (8597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235746841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452235733311 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8597:ℚ)^(-2:ℤ) : ℝ) = ((8597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1070 : ((((113058940091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8599, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8597 < q → q < 8599 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8599).mp (by decide +kernel))) hgap
  have hprev := s2L_1069
  have hrat : ((113058940091 : ℚ) / 250000000000) ≤ ((452235746841 : ℚ) / 1000000000000) + (8599:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058940091 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452235746841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8599:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8599:ℚ)^(-2:ℤ) : ℝ) = ((8599:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1071 : ((((14132367933 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8609, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8599 < q → q < 8609 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8609).mp (by decide +kernel))) hgap
  have hprev := s2L_1070
  have hrat : ((14132367933 : ℚ) / 31250000000) ≤ ((113058940091 : ℚ) / 250000000000) + (8609:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132367933 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113058940091 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8609:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8609:ℚ)^(-2:ℤ) : ℝ) = ((8609:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1072 : ((((56529473413 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8609 < q → q < 8623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8623).mp (by decide +kernel))) hgap
  have hprev := s2L_1071
  have hrat : ((56529473413 : ℚ) / 125000000000) ≤ ((14132367933 : ℚ) / 31250000000) + (8623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529473413 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((14132367933 : ℚ) / 31250000000) : ℚ) : ℝ) + ((8623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8623:ℚ)^(-2:ℤ) : ℝ) = ((8623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1073 : ((((22611790037 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8623 < q → q < 8627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8627).mp (by decide +kernel))) hgap
  have hprev := s2L_1072
  have hrat : ((22611790037 : ℚ) / 50000000000) ≤ ((56529473413 : ℚ) / 125000000000) + (8627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611790037 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56529473413 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8627:ℚ)^(-2:ℤ) : ℝ) = ((8627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1074 : ((((45223581417 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8627 < q → q < 8629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8629).mp (by decide +kernel))) hgap
  have hprev := s2L_1073
  have hrat : ((45223581417 : ℚ) / 100000000000) ≤ ((22611790037 : ℚ) / 50000000000) + (8629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223581417 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22611790037 : ℚ) / 50000000000) : ℚ) : ℝ) + ((8629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8629:ℚ)^(-2:ℤ) : ℝ) = ((8629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1075 : ((((226117913781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8629 < q → q < 8641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8641).mp (by decide +kernel))) hgap
  have hprev := s2L_1074
  have hrat : ((226117913781 : ℚ) / 500000000000) ≤ ((45223581417 : ℚ) / 100000000000) + (8641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117913781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45223581417 : ℚ) / 100000000000) : ℚ) : ℝ) + ((8641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8641:ℚ)^(-2:ℤ) : ℝ) = ((8641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1076 : ((((56529480117 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8641 < q → q < 8647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8647).mp (by decide +kernel))) hgap
  have hprev := s2L_1075
  have hrat : ((56529480117 : ℚ) / 125000000000) ≤ ((226117913781 : ℚ) / 500000000000) + (8647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529480117 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226117913781 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8647:ℚ)^(-2:ℤ) : ℝ) = ((8647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1077 : ((((22611792713 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8647 < q → q < 8663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8663).mp (by decide +kernel))) hgap
  have hprev := s2L_1076
  have hrat : ((22611792713 : ℚ) / 50000000000) ≤ ((56529480117 : ℚ) / 125000000000) + (8663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611792713 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56529480117 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8663:ℚ)^(-2:ℤ) : ℝ) = ((8663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1078 : ((((226117933783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8669, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8663 < q → q < 8669 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8669).mp (by decide +kernel))) hgap
  have hprev := s2L_1077
  have hrat : ((226117933783 : ℚ) / 500000000000) ≤ ((22611792713 : ℚ) / 50000000000) + (8669:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117933783 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22611792713 : ℚ) / 50000000000) : ℚ) : ℝ) + ((8669:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8669:ℚ)^(-2:ℤ) : ℝ) = ((8669:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1079 : ((((452235880847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8669 < q → q < 8677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8677).mp (by decide +kernel))) hgap
  have hprev := s2L_1078
  have hrat : ((452235880847 : ℚ) / 1000000000000) ≤ ((226117933783 : ℚ) / 500000000000) + (8677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235880847 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226117933783 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8677:ℚ)^(-2:ℤ) : ℝ) = ((8677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1080 : ((((113058973529 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8677 < q → q < 8681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8681).mp (by decide +kernel))) hgap
  have hprev := s2L_1079
  have hrat : ((113058973529 : ℚ) / 250000000000) ≤ ((452235880847 : ℚ) / 1000000000000) + (8681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058973529 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452235880847 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8681:ℚ)^(-2:ℤ) : ℝ) = ((8681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1081 : ((((452235907361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8681 < q → q < 8689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8689).mp (by decide +kernel))) hgap
  have hprev := s2L_1080
  have hrat : ((452235907361 : ℚ) / 1000000000000) ≤ ((113058973529 : ℚ) / 250000000000) + (8689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452235907361 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113058973529 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8689:ℚ)^(-2:ℤ) : ℝ) = ((8689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1082 : ((((226117960297 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8693, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8689 < q → q < 8693 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8693).mp (by decide +kernel))) hgap
  have hprev := s2L_1081
  have hrat : ((226117960297 : ℚ) / 500000000000) ≤ ((452235907361 : ℚ) / 1000000000000) + (8693:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117960297 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452235907361 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8693:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8693:ℚ)^(-2:ℤ) : ℝ) = ((8693:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1083 : ((((28264745863 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8693 < q → q < 8699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8699).mp (by decide +kernel))) hgap
  have hprev := s2L_1082
  have hrat : ((28264745863 : ℚ) / 62500000000) ≤ ((226117960297 : ℚ) / 500000000000) + (8699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264745863 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226117960297 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8699:ℚ)^(-2:ℤ) : ℝ) = ((8699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1084 : ((((226117973499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8707, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8699 < q → q < 8707 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8707).mp (by decide +kernel))) hgap
  have hprev := s2L_1083
  have hrat : ((226117973499 : ℚ) / 500000000000) ≤ ((28264745863 : ℚ) / 62500000000) + (8707:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117973499 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264745863 : ℚ) / 62500000000) : ℚ) : ℝ) + ((8707:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8707:ℚ)^(-2:ℤ) : ℝ) = ((8707:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1085 : ((((45223596017 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8707 < q → q < 8713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8713).mp (by decide +kernel))) hgap
  have hprev := s2L_1084
  have hrat : ((45223596017 : ℚ) / 100000000000) ≤ ((226117973499 : ℚ) / 500000000000) + (8713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223596017 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226117973499 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8713:ℚ)^(-2:ℤ) : ℝ) = ((8713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1086 : ((((113058993331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8713 < q → q < 8719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8719).mp (by decide +kernel))) hgap
  have hprev := s2L_1085
  have hrat : ((113058993331 : ℚ) / 250000000000) ≤ ((45223596017 : ℚ) / 100000000000) + (8719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113058993331 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((45223596017 : ℚ) / 100000000000) : ℚ) : ℝ) + ((8719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8719:ℚ)^(-2:ℤ) : ℝ) = ((8719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1087 : ((((226117993221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8719 < q → q < 8731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8731).mp (by decide +kernel))) hgap
  have hprev := s2L_1086
  have hrat : ((226117993221 : ℚ) / 500000000000) ≤ ((113058993331 : ℚ) / 250000000000) + (8731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117993221 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113058993331 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8731:ℚ)^(-2:ℤ) : ℝ) = ((8731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1088 : ((((226117999771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8737, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8731 < q → q < 8737 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8737).mp (by decide +kernel))) hgap
  have hprev := s2L_1087
  have hrat : ((226117999771 : ℚ) / 500000000000) ≤ ((226117993221 : ℚ) / 500000000000) + (8737:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226117999771 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226117993221 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8737:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8737:ℚ)^(-2:ℤ) : ℝ) = ((8737:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1089 : ((((45223601263 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8741, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8737 < q → q < 8741 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8741).mp (by decide +kernel))) hgap
  have hprev := s2L_1088
  have hrat : ((45223601263 : ℚ) / 100000000000) ≤ ((226117999771 : ℚ) / 500000000000) + (8741:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223601263 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226117999771 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8741:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8741:ℚ)^(-2:ℤ) : ℝ) = ((8741:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1090 : ((((4522360257 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8747, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8741 < q → q < 8747 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8747).mp (by decide +kernel))) hgap
  have hprev := s2L_1089
  have hrat : ((4522360257 : ℚ) / 10000000000) ≤ ((45223601263 : ℚ) / 100000000000) + (8747:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522360257 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((45223601263 : ℚ) / 100000000000) : ℚ) : ℝ) + ((8747:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8747:ℚ)^(-2:ℤ) : ℝ) = ((8747:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1091 : ((((14132376211 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8747 < q → q < 8753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8753).mp (by decide +kernel))) hgap
  have hprev := s2L_1090
  have hrat : ((14132376211 : ℚ) / 31250000000) ≤ ((4522360257 : ℚ) / 10000000000) + (8753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132376211 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((4522360257 : ℚ) / 10000000000) : ℚ) : ℝ) + ((8753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8753:ℚ)^(-2:ℤ) : ℝ) = ((8753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1092 : ((((22611802589 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8761, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8753 < q → q < 8761 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8761).mp (by decide +kernel))) hgap
  have hprev := s2L_1091
  have hrat : ((22611802589 : ℚ) / 50000000000) ≤ ((14132376211 : ℚ) / 31250000000) + (8761:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611802589 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((14132376211 : ℚ) / 31250000000) : ℚ) : ℝ) + ((8761:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8761:ℚ)^(-2:ℤ) : ℝ) = ((8761:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1093 : ((((90447212951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8761 < q → q < 8779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8779).mp (by decide +kernel))) hgap
  have hprev := s2L_1092
  have hrat : ((90447212951 : ℚ) / 200000000000) ≤ ((22611802589 : ℚ) / 50000000000) + (8779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447212951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22611802589 : ℚ) / 50000000000) : ℚ) : ℝ) + ((8779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8779:ℚ)^(-2:ℤ) : ℝ) = ((8779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1094 : ((((226118038859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8779 < q → q < 8783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8783).mp (by decide +kernel))) hgap
  have hprev := s2L_1093
  have hrat : ((226118038859 : ℚ) / 500000000000) ≤ ((90447212951 : ℚ) / 200000000000) + (8783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118038859 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447212951 : ℚ) / 200000000000) : ℚ) : ℝ) + ((8783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8783:ℚ)^(-2:ℤ) : ℝ) = ((8783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1095 : ((((226118045311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8783 < q → q < 8803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8803).mp (by decide +kernel))) hgap
  have hprev := s2L_1094
  have hrat : ((226118045311 : ℚ) / 500000000000) ≤ ((226118038859 : ℚ) / 500000000000) + (8803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118045311 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118038859 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8803:ℚ)^(-2:ℤ) : ℝ) = ((8803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1096 : ((((226118051757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8803 < q → q < 8807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8807).mp (by decide +kernel))) hgap
  have hprev := s2L_1095
  have hrat : ((226118051757 : ℚ) / 500000000000) ≤ ((226118045311 : ℚ) / 500000000000) + (8807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118051757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118045311 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8807:ℚ)^(-2:ℤ) : ℝ) = ((8807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1097 : ((((452236116371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8819, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8807 < q → q < 8819 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8819).mp (by decide +kernel))) hgap
  have hprev := s2L_1096
  have hrat : ((452236116371 : ℚ) / 1000000000000) ≤ ((226118051757 : ℚ) / 500000000000) + (8819:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236116371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118051757 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8819:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8819:ℚ)^(-2:ℤ) : ℝ) = ((8819:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1098 : ((((226118064611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8819 < q → q < 8821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8821).mp (by decide +kernel))) hgap
  have hprev := s2L_1097
  have hrat : ((226118064611 : ℚ) / 500000000000) ≤ ((452236116371 : ℚ) / 1000000000000) + (8821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118064611 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236116371 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8821:ℚ)^(-2:ℤ) : ℝ) = ((8821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1099 : ((((113059035511 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8821 < q → q < 8831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8831).mp (by decide +kernel))) hgap
  have hprev := s2L_1098
  have hrat : ((113059035511 : ℚ) / 250000000000) ≤ ((226118064611 : ℚ) / 500000000000) + (8831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059035511 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226118064611 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8831:ℚ)^(-2:ℤ) : ℝ) = ((8831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1100 : ((((452236154849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8831 < q → q < 8837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8837).mp (by decide +kernel))) hgap
  have hprev := s2L_1099
  have hrat : ((452236154849 : ℚ) / 1000000000000) ≤ ((113059035511 : ℚ) / 250000000000) + (8837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236154849 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059035511 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8837:ℚ)^(-2:ℤ) : ℝ) = ((8837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1101 : ((((14132380239 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8837 < q → q < 8839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8839).mp (by decide +kernel))) hgap
  have hprev := s2L_1100
  have hrat : ((14132380239 : ℚ) / 31250000000) ≤ ((452236154849 : ℚ) / 1000000000000) + (8839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132380239 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452236154849 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8839:ℚ)^(-2:ℤ) : ℝ) = ((8839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1102 : ((((226118090209 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8849, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8839 < q → q < 8849 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8849).mp (by decide +kernel))) hgap
  have hprev := s2L_1101
  have hrat : ((226118090209 : ℚ) / 500000000000) ≤ ((14132380239 : ℚ) / 31250000000) + (8849:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118090209 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((14132380239 : ℚ) / 31250000000) : ℚ) : ℝ) + ((8849:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8849:ℚ)^(-2:ℤ) : ℝ) = ((8849:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1103 : ((((226118096577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8849 < q → q < 8861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8861).mp (by decide +kernel))) hgap
  have hprev := s2L_1102
  have hrat : ((226118096577 : ℚ) / 500000000000) ≤ ((226118090209 : ℚ) / 500000000000) + (8861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118096577 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118090209 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8861:ℚ)^(-2:ℤ) : ℝ) = ((8861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1104 : ((((113059051471 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8861 < q → q < 8863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8863).mp (by decide +kernel))) hgap
  have hprev := s2L_1103
  have hrat : ((113059051471 : ℚ) / 250000000000) ≤ ((226118096577 : ℚ) / 500000000000) + (8863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059051471 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226118096577 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8863:ℚ)^(-2:ℤ) : ℝ) = ((8863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1105 : ((((226118109301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8863 < q → q < 8867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8867).mp (by decide +kernel))) hgap
  have hprev := s2L_1104
  have hrat : ((226118109301 : ℚ) / 500000000000) ≤ ((113059051471 : ℚ) / 250000000000) + (8867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118109301 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059051471 : ℚ) / 250000000000) : ℚ) : ℝ) + ((8867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8867:ℚ)^(-2:ℤ) : ℝ) = ((8867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1106 : ((((452236231263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8867 < q → q < 8887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8887).mp (by decide +kernel))) hgap
  have hprev := s2L_1105
  have hrat : ((452236231263 : ℚ) / 1000000000000) ≤ ((226118109301 : ℚ) / 500000000000) + (8887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236231263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118109301 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8887:ℚ)^(-2:ℤ) : ℝ) = ((8887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1107 : ((((452236243907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8887 < q → q < 8893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8893).mp (by decide +kernel))) hgap
  have hprev := s2L_1106
  have hrat : ((452236243907 : ℚ) / 1000000000000) ≤ ((452236231263 : ℚ) / 1000000000000) + (8893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236243907 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236231263 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8893:ℚ)^(-2:ℤ) : ℝ) = ((8893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1108 : ((((226118128233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8893 < q → q < 8923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8923).mp (by decide +kernel))) hgap
  have hprev := s2L_1107
  have hrat : ((226118128233 : ℚ) / 500000000000) ≤ ((452236243907 : ℚ) / 1000000000000) + (8923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118128233 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236243907 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8923:ℚ)^(-2:ℤ) : ℝ) = ((8923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1109 : ((((28264766813 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8923 < q → q < 8929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8929).mp (by decide +kernel))) hgap
  have hprev := s2L_1108
  have hrat : ((28264766813 : ℚ) / 62500000000) ≤ ((226118128233 : ℚ) / 500000000000) + (8929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264766813 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226118128233 : ℚ) / 500000000000) : ℚ) : ℝ) + ((8929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8929:ℚ)^(-2:ℤ) : ℝ) = ((8929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1110 : ((((452236281539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8929 < q → q < 8933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8933).mp (by decide +kernel))) hgap
  have hprev := s2L_1109
  have hrat : ((452236281539 : ℚ) / 1000000000000) ≤ ((28264766813 : ℚ) / 62500000000) + (8933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236281539 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28264766813 : ℚ) / 62500000000) : ℚ) : ℝ) + ((8933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8933:ℚ)^(-2:ℤ) : ℝ) = ((8933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1111 : ((((14132384189 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8933 < q → q < 8941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8941).mp (by decide +kernel))) hgap
  have hprev := s2L_1110
  have hrat : ((14132384189 : ℚ) / 31250000000) ≤ ((452236281539 : ℚ) / 1000000000000) + (8941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132384189 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((452236281539 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8941:ℚ)^(-2:ℤ) : ℝ) = ((8941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1112 : ((((452236306529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8951, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8941 < q → q < 8951 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8951).mp (by decide +kernel))) hgap
  have hprev := s2L_1111
  have hrat : ((452236306529 : ℚ) / 1000000000000) ≤ ((14132384189 : ℚ) / 31250000000) + (8951:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236306529 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132384189 : ℚ) / 31250000000) : ℚ) : ℝ) + ((8951:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8951:ℚ)^(-2:ℤ) : ℝ) = ((8951:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1113 : ((((1766548121 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8963, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8951 < q → q < 8963 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8963).mp (by decide +kernel))) hgap
  have hprev := s2L_1112
  have hrat : ((1766548121 : ℚ) / 3906250000) ≤ ((452236306529 : ℚ) / 1000000000000) + (8963:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1766548121 : ℚ) / 3906250000) : ℚ) : ℝ) ≤ ((((452236306529 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8963:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8963:ℚ)^(-2:ℤ) : ℝ) = ((8963:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1114 : ((((452236331407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8963 < q → q < 8969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8969).mp (by decide +kernel))) hgap
  have hprev := s2L_1113
  have hrat : ((452236331407 : ℚ) / 1000000000000) ≤ ((1766548121 : ℚ) / 3906250000) + (8969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236331407 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1766548121 : ℚ) / 3906250000) : ℚ) : ℝ) + ((8969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8969:ℚ)^(-2:ℤ) : ℝ) = ((8969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1115 : ((((56529542979 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8969 < q → q < 8971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8971).mp (by decide +kernel))) hgap
  have hprev := s2L_1114
  have hrat : ((56529542979 : ℚ) / 125000000000) ≤ ((452236331407 : ℚ) / 1000000000000) + (8971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529542979 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452236331407 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((8971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8971:ℚ)^(-2:ℤ) : ℝ) = ((8971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1116 : ((((22611817809 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 8999, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8971 < q → q < 8999 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 8999).mp (by decide +kernel))) hgap
  have hprev := s2L_1115
  have hrat : ((22611817809 : ℚ) / 50000000000) ≤ ((56529542979 : ℚ) / 125000000000) + (8999:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611817809 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((56529542979 : ℚ) / 125000000000) : ℚ) : ℝ) + ((8999:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((8999:ℚ)^(-2:ℤ) : ℝ) = ((8999:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1117 : ((((226118184261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 8999 < q → q < 9001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9001).mp (by decide +kernel))) hgap
  have hprev := s2L_1116
  have hrat : ((226118184261 : ℚ) / 500000000000) ≤ ((22611817809 : ℚ) / 50000000000) + (9001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118184261 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22611817809 : ℚ) / 50000000000) : ℚ) : ℝ) + ((9001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9001:ℚ)^(-2:ℤ) : ℝ) = ((9001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1118 : ((((28264773803 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9001 < q → q < 9007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9007).mp (by decide +kernel))) hgap
  have hprev := s2L_1117
  have hrat : ((28264773803 : ℚ) / 62500000000) ≤ ((226118184261 : ℚ) / 500000000000) + (9007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264773803 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226118184261 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9007:ℚ)^(-2:ℤ) : ℝ) = ((9007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1119 : ((((452236393163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9007 < q → q < 9011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9011).mp (by decide +kernel))) hgap
  have hprev := s2L_1118
  have hrat : ((452236393163 : ℚ) / 1000000000000) ≤ ((28264773803 : ℚ) / 62500000000) + (9011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236393163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28264773803 : ℚ) / 62500000000) : ℚ) : ℝ) + ((9011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9011:ℚ)^(-2:ℤ) : ℝ) = ((9011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1120 : ((((452236405473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9013, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9011 < q → q < 9013 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9013).mp (by decide +kernel))) hgap
  have hprev := s2L_1119
  have hrat : ((452236405473 : ℚ) / 1000000000000) ≤ ((452236393163 : ℚ) / 1000000000000) + (9013:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236405473 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236393163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9013:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9013:ℚ)^(-2:ℤ) : ℝ) = ((9013:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1121 : ((((452236417739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9029, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9013 < q → q < 9029 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9029).mp (by decide +kernel))) hgap
  have hprev := s2L_1120
  have hrat : ((452236417739 : ℚ) / 1000000000000) ≤ ((452236405473 : ℚ) / 1000000000000) + (9029:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236417739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236405473 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9029:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9029:ℚ)^(-2:ℤ) : ℝ) = ((9029:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1122 : ((((113059107493 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9029 < q → q < 9041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9041).mp (by decide +kernel))) hgap
  have hprev := s2L_1121
  have hrat : ((113059107493 : ℚ) / 250000000000) ≤ ((452236417739 : ℚ) / 1000000000000) + (9041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059107493 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452236417739 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9041:ℚ)^(-2:ℤ) : ℝ) = ((9041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1123 : ((((2261182211 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9041 < q → q < 9043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9043).mp (by decide +kernel))) hgap
  have hprev := s2L_1122
  have hrat : ((2261182211 : ℚ) / 5000000000) ≤ ((113059107493 : ℚ) / 250000000000) + (9043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261182211 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((113059107493 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9043:ℚ)^(-2:ℤ) : ℝ) = ((9043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1124 : ((((113059113603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9043 < q → q < 9049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9049).mp (by decide +kernel))) hgap
  have hprev := s2L_1123
  have hrat : ((113059113603 : ℚ) / 250000000000) ≤ ((2261182211 : ℚ) / 5000000000) + (9049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059113603 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((2261182211 : ℚ) / 5000000000) : ℚ) : ℝ) + ((9049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9049:ℚ)^(-2:ℤ) : ℝ) = ((9049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1125 : ((((452236466597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9049 < q → q < 9059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9059).mp (by decide +kernel))) hgap
  have hprev := s2L_1124
  have hrat : ((452236466597 : ℚ) / 1000000000000) ≤ ((113059113603 : ℚ) / 250000000000) + (9059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236466597 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059113603 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9059:ℚ)^(-2:ℤ) : ℝ) = ((9059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1126 : ((((11305911969 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9059 < q → q < 9067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9067).mp (by decide +kernel))) hgap
  have hprev := s2L_1125
  have hrat : ((11305911969 : ℚ) / 25000000000) ≤ ((452236466597 : ℚ) / 1000000000000) + (9067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305911969 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452236466597 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9067:ℚ)^(-2:ℤ) : ℝ) = ((9067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1127 : ((((452236490859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9067 < q → q < 9091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9091).mp (by decide +kernel))) hgap
  have hprev := s2L_1126
  have hrat : ((452236490859 : ℚ) / 1000000000000) ≤ ((11305911969 : ℚ) / 25000000000) + (9091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236490859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11305911969 : ℚ) / 25000000000) : ℚ) : ℝ) + ((9091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9091:ℚ)^(-2:ℤ) : ℝ) = ((9091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1128 : ((((226118251463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9091 < q → q < 9103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9103).mp (by decide +kernel))) hgap
  have hprev := s2L_1127
  have hrat : ((226118251463 : ℚ) / 500000000000) ≤ ((452236490859 : ℚ) / 1000000000000) + (9103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118251463 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236490859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9103:ℚ)^(-2:ℤ) : ℝ) = ((9103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1129 : ((((452236514977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9103 < q → q < 9109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9109).mp (by decide +kernel))) hgap
  have hprev := s2L_1128
  have hrat : ((452236514977 : ℚ) / 1000000000000) ≤ ((226118251463 : ℚ) / 500000000000) + (9109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236514977 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118251463 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9109:ℚ)^(-2:ℤ) : ℝ) = ((9109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1130 : ((((452236526981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9109 < q → q < 9127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9127).mp (by decide +kernel))) hgap
  have hprev := s2L_1129
  have hrat : ((452236526981 : ℚ) / 1000000000000) ≤ ((452236514977 : ℚ) / 1000000000000) + (9127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236526981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236514977 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9127:ℚ)^(-2:ℤ) : ℝ) = ((9127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1131 : ((((452236538969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9127 < q → q < 9133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9133).mp (by decide +kernel))) hgap
  have hprev := s2L_1130
  have hrat : ((452236538969 : ℚ) / 1000000000000) ≤ ((452236526981 : ℚ) / 1000000000000) + (9133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236538969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236526981 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9133:ℚ)^(-2:ℤ) : ℝ) = ((9133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1132 : ((((452236550947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9137, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9133 < q → q < 9137 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9137).mp (by decide +kernel))) hgap
  have hprev := s2L_1131
  have hrat : ((452236550947 : ℚ) / 1000000000000) ≤ ((452236538969 : ℚ) / 1000000000000) + (9137:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236550947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236538969 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9137:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9137:ℚ)^(-2:ℤ) : ℝ) = ((9137:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1133 : ((((56529570361 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9137 < q → q < 9151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9151).mp (by decide +kernel))) hgap
  have hprev := s2L_1132
  have hrat : ((56529570361 : ℚ) / 125000000000) ≤ ((452236550947 : ℚ) / 1000000000000) + (9151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529570361 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452236550947 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9151:ℚ)^(-2:ℤ) : ℝ) = ((9151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1134 : ((((452236574813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9151 < q → q < 9157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9157).mp (by decide +kernel))) hgap
  have hprev := s2L_1133
  have hrat : ((452236574813 : ℚ) / 1000000000000) ≤ ((56529570361 : ℚ) / 125000000000) + (9157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236574813 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529570361 : ℚ) / 125000000000) : ℚ) : ℝ) + ((9157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9157:ℚ)^(-2:ℤ) : ℝ) = ((9157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1135 : ((((56529573341 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9157 < q → q < 9161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9161).mp (by decide +kernel))) hgap
  have hprev := s2L_1134
  have hrat : ((56529573341 : ℚ) / 125000000000) ≤ ((452236574813 : ℚ) / 1000000000000) + (9161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529573341 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452236574813 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9161:ℚ)^(-2:ℤ) : ℝ) = ((9161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1136 : ((((113059149653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9161 < q → q < 9173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9173).mp (by decide +kernel))) hgap
  have hprev := s2L_1135
  have hrat : ((113059149653 : ℚ) / 250000000000) ≤ ((56529573341 : ℚ) / 125000000000) + (9173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059149653 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56529573341 : ℚ) / 125000000000) : ℚ) : ℝ) + ((9173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9173:ℚ)^(-2:ℤ) : ℝ) = ((9173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1137 : ((((18089464419 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9173 < q → q < 9181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9181).mp (by decide +kernel))) hgap
  have hprev := s2L_1136
  have hrat : ((18089464419 : ℚ) / 40000000000) ≤ ((113059149653 : ℚ) / 250000000000) + (9181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089464419 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113059149653 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9181:ℚ)^(-2:ℤ) : ℝ) = ((9181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1138 : ((((452236622323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9181 < q → q < 9187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9187).mp (by decide +kernel))) hgap
  have hprev := s2L_1137
  have hrat : ((452236622323 : ℚ) / 1000000000000) ≤ ((18089464419 : ℚ) / 40000000000) + (9187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236622323 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089464419 : ℚ) / 40000000000) : ℚ) : ℝ) + ((9187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9187:ℚ)^(-2:ℤ) : ℝ) = ((9187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1139 : ((((22611831707 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9199, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9187 < q → q < 9199 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9199).mp (by decide +kernel))) hgap
  have hprev := s2L_1138
  have hrat : ((22611831707 : ℚ) / 50000000000) ≤ ((452236622323 : ℚ) / 1000000000000) + (9199:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611831707 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452236622323 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9199:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9199:ℚ)^(-2:ℤ) : ℝ) = ((9199:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1140 : ((((452236645947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9199 < q → q < 9203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9203).mp (by decide +kernel))) hgap
  have hprev := s2L_1139
  have hrat : ((452236645947 : ℚ) / 1000000000000) ≤ ((22611831707 : ℚ) / 50000000000) + (9203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236645947 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22611831707 : ℚ) / 50000000000) : ℚ) : ℝ) + ((9203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9203:ℚ)^(-2:ℤ) : ℝ) = ((9203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1141 : ((((226118328869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9209, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9203 < q → q < 9209 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9209).mp (by decide +kernel))) hgap
  have hprev := s2L_1140
  have hrat : ((226118328869 : ℚ) / 500000000000) ≤ ((452236645947 : ℚ) / 1000000000000) + (9209:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118328869 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236645947 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9209:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9209:ℚ)^(-2:ℤ) : ℝ) = ((9209:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1142 : ((((226118334749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9221, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9209 < q → q < 9221 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9221).mp (by decide +kernel))) hgap
  have hprev := s2L_1141
  have hrat : ((226118334749 : ℚ) / 500000000000) ≤ ((226118328869 : ℚ) / 500000000000) + (9221:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118334749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118328869 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9221:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9221:ℚ)^(-2:ℤ) : ℝ) = ((9221:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1143 : ((((452236681243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9221 < q → q < 9227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9227).mp (by decide +kernel))) hgap
  have hprev := s2L_1142
  have hrat : ((452236681243 : ℚ) / 1000000000000) ≤ ((226118334749 : ℚ) / 500000000000) + (9227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236681243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118334749 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9227:ℚ)^(-2:ℤ) : ℝ) = ((9227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1144 : ((((226118346479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9227 < q → q < 9239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9239).mp (by decide +kernel))) hgap
  have hprev := s2L_1143
  have hrat : ((226118346479 : ℚ) / 500000000000) ≤ ((452236681243 : ℚ) / 1000000000000) + (9239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118346479 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236681243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9239:ℚ)^(-2:ℤ) : ℝ) = ((9239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1145 : ((((113059176167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9239 < q → q < 9241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9241).mp (by decide +kernel))) hgap
  have hprev := s2L_1144
  have hrat : ((113059176167 : ℚ) / 250000000000) ≤ ((226118346479 : ℚ) / 500000000000) + (9241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059176167 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226118346479 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9241:ℚ)^(-2:ℤ) : ℝ) = ((9241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1146 : ((((452236716337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9241 < q → q < 9257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9257).mp (by decide +kernel))) hgap
  have hprev := s2L_1145
  have hrat : ((452236716337 : ℚ) / 1000000000000) ≤ ((113059176167 : ℚ) / 250000000000) + (9257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236716337 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059176167 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9257:ℚ)^(-2:ℤ) : ℝ) = ((9257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1147 : ((((113059181989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9257 < q → q < 9277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9277).mp (by decide +kernel))) hgap
  have hprev := s2L_1146
  have hrat : ((113059181989 : ℚ) / 250000000000) ≤ ((452236716337 : ℚ) / 1000000000000) + (9277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059181989 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452236716337 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9277:ℚ)^(-2:ℤ) : ℝ) = ((9277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1148 : ((((90447347913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9277 < q → q < 9281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9281).mp (by decide +kernel))) hgap
  have hprev := s2L_1147
  have hrat : ((90447347913 : ℚ) / 200000000000) ≤ ((113059181989 : ℚ) / 250000000000) + (9281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447347913 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113059181989 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9281:ℚ)^(-2:ℤ) : ℝ) = ((9281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1149 : ((((452236751169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9283, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9281 < q → q < 9283 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9283).mp (by decide +kernel))) hgap
  have hprev := s2L_1148
  have hrat : ((452236751169 : ℚ) / 1000000000000) ≤ ((90447347913 : ℚ) / 200000000000) + (9283:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236751169 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447347913 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9283:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9283:ℚ)^(-2:ℤ) : ℝ) = ((9283:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1150 : ((((113059190687 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9293, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9283 < q → q < 9293 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9293).mp (by decide +kernel))) hgap
  have hprev := s2L_1149
  have hrat : ((113059190687 : ℚ) / 250000000000) ≤ ((452236751169 : ℚ) / 1000000000000) + (9293:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059190687 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452236751169 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9293:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9293:ℚ)^(-2:ℤ) : ℝ) = ((9293:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1151 : ((((226118387141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9293 < q → q < 9311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9311).mp (by decide +kernel))) hgap
  have hprev := s2L_1150
  have hrat : ((226118387141 : ℚ) / 500000000000) ≤ ((113059190687 : ℚ) / 250000000000) + (9311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118387141 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059190687 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9311:ℚ)^(-2:ℤ) : ℝ) = ((9311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1152 : ((((113059196449 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9319, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9311 < q → q < 9319 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9319).mp (by decide +kernel))) hgap
  have hprev := s2L_1151
  have hrat : ((113059196449 : ℚ) / 250000000000) ≤ ((226118387141 : ℚ) / 500000000000) + (9319:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059196449 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226118387141 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9319:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9319:ℚ)^(-2:ℤ) : ℝ) = ((9319:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1153 : ((((452236797301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9319 < q → q < 9323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9323).mp (by decide +kernel))) hgap
  have hprev := s2L_1152
  have hrat : ((452236797301 : ℚ) / 1000000000000) ≤ ((113059196449 : ℚ) / 250000000000) + (9323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236797301 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059196449 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9323:ℚ)^(-2:ℤ) : ℝ) = ((9323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1154 : ((((452236808771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9323 < q → q < 9337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9337).mp (by decide +kernel))) hgap
  have hprev := s2L_1153
  have hrat : ((452236808771 : ℚ) / 1000000000000) ≤ ((452236797301 : ℚ) / 1000000000000) + (9337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236808771 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236797301 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9337:ℚ)^(-2:ℤ) : ℝ) = ((9337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1155 : ((((452236820231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9341, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9337 < q → q < 9341 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9341).mp (by decide +kernel))) hgap
  have hprev := s2L_1154
  have hrat : ((452236820231 : ℚ) / 1000000000000) ≤ ((452236808771 : ℚ) / 1000000000000) + (9341:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236820231 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236808771 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9341:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9341:ℚ)^(-2:ℤ) : ℝ) = ((9341:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1156 : ((((226118415843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9341 < q → q < 9343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9343).mp (by decide +kernel))) hgap
  have hprev := s2L_1155
  have hrat : ((226118415843 : ℚ) / 500000000000) ≤ ((452236820231 : ℚ) / 1000000000000) + (9343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118415843 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236820231 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9343:ℚ)^(-2:ℤ) : ℝ) = ((9343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1157 : ((((452236843127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9349, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9343 < q → q < 9349 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9349).mp (by decide +kernel))) hgap
  have hprev := s2L_1156
  have hrat : ((452236843127 : ℚ) / 1000000000000) ≤ ((226118415843 : ℚ) / 500000000000) + (9349:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236843127 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118415843 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9349:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9349:ℚ)^(-2:ℤ) : ℝ) = ((9349:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1158 : ((((226118427257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9371, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9349 < q → q < 9371 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9371).mp (by decide +kernel))) hgap
  have hprev := s2L_1157
  have hrat : ((226118427257 : ℚ) / 500000000000) ≤ ((452236843127 : ℚ) / 1000000000000) + (9371:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118427257 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452236843127 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9371:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9371:ℚ)^(-2:ℤ) : ℝ) = ((9371:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1159 : ((((226118432943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9371 < q → q < 9377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9377).mp (by decide +kernel))) hgap
  have hprev := s2L_1158
  have hrat : ((226118432943 : ℚ) / 500000000000) ≤ ((226118427257 : ℚ) / 500000000000) + (9377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118432943 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118427257 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9377:ℚ)^(-2:ℤ) : ℝ) = ((9377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1160 : ((((18089475089 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9377 < q → q < 9391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9391).mp (by decide +kernel))) hgap
  have hprev := s2L_1159
  have hrat : ((18089475089 : ℚ) / 40000000000) ≤ ((226118432943 : ℚ) / 500000000000) + (9391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089475089 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226118432943 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9391:ℚ)^(-2:ℤ) : ℝ) = ((9391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1161 : ((((452236888549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9391 < q → q < 9397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9397).mp (by decide +kernel))) hgap
  have hprev := s2L_1160
  have hrat : ((452236888549 : ℚ) / 1000000000000) ≤ ((18089475089 : ℚ) / 40000000000) + (9397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236888549 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089475089 : ℚ) / 40000000000) : ℚ) : ℝ) + ((9397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9397:ℚ)^(-2:ℤ) : ℝ) = ((9397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1162 : ((((452236899859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9403, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9397 < q → q < 9403 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9403).mp (by decide +kernel))) hgap
  have hprev := s2L_1161
  have hrat : ((452236899859 : ℚ) / 1000000000000) ≤ ((452236888549 : ℚ) / 1000000000000) + (9403:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236899859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236888549 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9403:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9403:ℚ)^(-2:ℤ) : ℝ) = ((9403:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1163 : ((((90447382229 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9403 < q → q < 9413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9413).mp (by decide +kernel))) hgap
  have hprev := s2L_1162
  have hrat : ((90447382229 : ℚ) / 200000000000) ≤ ((452236899859 : ℚ) / 1000000000000) + (9413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447382229 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452236899859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9413:ℚ)^(-2:ℤ) : ℝ) = ((9413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1164 : ((((28264807651 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9419, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9413 < q → q < 9419 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9419).mp (by decide +kernel))) hgap
  have hprev := s2L_1163
  have hrat : ((28264807651 : ℚ) / 62500000000) ≤ ((90447382229 : ℚ) / 200000000000) + (9419:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264807651 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90447382229 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9419:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9419:ℚ)^(-2:ℤ) : ℝ) = ((9419:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1165 : ((((226118466841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9419 < q → q < 9421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9421).mp (by decide +kernel))) hgap
  have hprev := s2L_1164
  have hrat : ((226118466841 : ℚ) / 500000000000) ≤ ((28264807651 : ℚ) / 62500000000) + (9421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118466841 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264807651 : ℚ) / 62500000000) : ℚ) : ℝ) + ((9421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9421:ℚ)^(-2:ℤ) : ℝ) = ((9421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1166 : ((((18089477797 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9431, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9421 < q → q < 9431 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9431).mp (by decide +kernel))) hgap
  have hprev := s2L_1165
  have hrat : ((18089477797 : ℚ) / 40000000000) ≤ ((226118466841 : ℚ) / 500000000000) + (9431:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089477797 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226118466841 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9431:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9431:ℚ)^(-2:ℤ) : ℝ) = ((9431:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1167 : ((((452236956163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9431 < q → q < 9433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9433).mp (by decide +kernel))) hgap
  have hprev := s2L_1166
  have hrat : ((452236956163 : ℚ) / 1000000000000) ≤ ((18089477797 : ℚ) / 40000000000) + (9433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236956163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089477797 : ℚ) / 40000000000) : ℚ) : ℝ) + ((9433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9433:ℚ)^(-2:ℤ) : ℝ) = ((9433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1168 : ((((452236967391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9433 < q → q < 9437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9437).mp (by decide +kernel))) hgap
  have hprev := s2L_1167
  have hrat : ((452236967391 : ℚ) / 1000000000000) ≤ ((452236956163 : ℚ) / 1000000000000) + (9437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452236967391 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452236956163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9437:ℚ)^(-2:ℤ) : ℝ) = ((9437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1169 : ((((90447395723 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9439, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9437 < q → q < 9439 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9439).mp (by decide +kernel))) hgap
  have hprev := s2L_1168
  have hrat : ((90447395723 : ℚ) / 200000000000) ≤ ((452236967391 : ℚ) / 1000000000000) + (9439:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447395723 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452236967391 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9439:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9439:ℚ)^(-2:ℤ) : ℝ) = ((9439:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1170 : ((((226118494893 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9461, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9439 < q → q < 9461 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9461).mp (by decide +kernel))) hgap
  have hprev := s2L_1169
  have hrat : ((226118494893 : ℚ) / 500000000000) ≤ ((90447395723 : ℚ) / 200000000000) + (9461:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118494893 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447395723 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9461:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9461:ℚ)^(-2:ℤ) : ℝ) = ((9461:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1171 : ((((452237000953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9461 < q → q < 9463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9463).mp (by decide +kernel))) hgap
  have hprev := s2L_1170
  have hrat : ((452237000953 : ℚ) / 1000000000000) ≤ ((226118494893 : ℚ) / 500000000000) + (9463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237000953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118494893 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9463:ℚ)^(-2:ℤ) : ℝ) = ((9463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1172 : ((((45223701211 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9463 < q → q < 9467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9467).mp (by decide +kernel))) hgap
  have hprev := s2L_1171
  have hrat : ((45223701211 : ℚ) / 100000000000) ≤ ((452237000953 : ℚ) / 1000000000000) + (9467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223701211 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452237000953 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9467:ℚ)^(-2:ℤ) : ℝ) = ((9467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1173 : ((((452237023253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9467 < q → q < 9473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9473).mp (by decide +kernel))) hgap
  have hprev := s2L_1172
  have hrat : ((452237023253 : ℚ) / 1000000000000) ≤ ((45223701211 : ℚ) / 100000000000) + (9473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237023253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223701211 : ℚ) / 100000000000) : ℚ) : ℝ) + ((9473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9473:ℚ)^(-2:ℤ) : ℝ) = ((9473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1174 : ((((226118517191 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9473 < q → q < 9479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9479).mp (by decide +kernel))) hgap
  have hprev := s2L_1173
  have hrat : ((226118517191 : ℚ) / 500000000000) ≤ ((452237023253 : ℚ) / 1000000000000) + (9479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118517191 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237023253 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9479:ℚ)^(-2:ℤ) : ℝ) = ((9479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1175 : ((((452237045483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9479 < q → q < 9491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9491).mp (by decide +kernel))) hgap
  have hprev := s2L_1174
  have hrat : ((452237045483 : ℚ) / 1000000000000) ≤ ((226118517191 : ℚ) / 500000000000) + (9491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237045483 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118517191 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9491:ℚ)^(-2:ℤ) : ℝ) = ((9491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1176 : ((((45223705657 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9491 < q → q < 9497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9497).mp (by decide +kernel))) hgap
  have hprev := s2L_1175
  have hrat : ((45223705657 : ℚ) / 100000000000) ≤ ((452237045483 : ℚ) / 1000000000000) + (9497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223705657 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452237045483 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9497:ℚ)^(-2:ℤ) : ℝ) = ((9497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1177 : ((((56529633453 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9497 < q → q < 9511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9511).mp (by decide +kernel))) hgap
  have hprev := s2L_1176
  have hrat : ((56529633453 : ℚ) / 125000000000) ≤ ((45223705657 : ℚ) / 100000000000) + (9511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529633453 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45223705657 : ℚ) / 100000000000) : ℚ) : ℝ) + ((9511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9511:ℚ)^(-2:ℤ) : ℝ) = ((9511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1178 : ((((90447415731 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9521, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9511 < q → q < 9521 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9521).mp (by decide +kernel))) hgap
  have hprev := s2L_1177
  have hrat : ((90447415731 : ℚ) / 200000000000) ≤ ((56529633453 : ℚ) / 125000000000) + (9521:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447415731 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56529633453 : ℚ) / 125000000000) : ℚ) : ℝ) + ((9521:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9521:ℚ)^(-2:ℤ) : ℝ) = ((9521:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1179 : ((((226118544829 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9533, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9521 < q → q < 9533 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9533).mp (by decide +kernel))) hgap
  have hprev := s2L_1178
  have hrat : ((226118544829 : ℚ) / 500000000000) ≤ ((90447415731 : ℚ) / 200000000000) + (9533:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118544829 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447415731 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9533:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9533:ℚ)^(-2:ℤ) : ℝ) = ((9533:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1180 : ((((452237100647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9533 < q → q < 9539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9539).mp (by decide +kernel))) hgap
  have hprev := s2L_1179
  have hrat : ((452237100647 : ℚ) / 1000000000000) ≤ ((226118544829 : ℚ) / 500000000000) + (9539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237100647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118544829 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9539:ℚ)^(-2:ℤ) : ℝ) = ((9539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1181 : ((((226118555809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9539 < q → q < 9547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9547).mp (by decide +kernel))) hgap
  have hprev := s2L_1180
  have hrat : ((226118555809 : ℚ) / 500000000000) ≤ ((452237100647 : ℚ) / 1000000000000) + (9547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118555809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237100647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9547:ℚ)^(-2:ℤ) : ℝ) = ((9547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1182 : ((((22611856129 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9547 < q → q < 9551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9551).mp (by decide +kernel))) hgap
  have hprev := s2L_1181
  have hrat : ((22611856129 : ℚ) / 50000000000) ≤ ((226118555809 : ℚ) / 500000000000) + (9551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611856129 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226118555809 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9551:ℚ)^(-2:ℤ) : ℝ) = ((9551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1183 : ((((22611856673 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9551 < q → q < 9587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9587).mp (by decide +kernel))) hgap
  have hprev := s2L_1182
  have hrat : ((22611856673 : ℚ) / 50000000000) ≤ ((22611856129 : ℚ) / 50000000000) + (9587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611856673 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((22611856129 : ℚ) / 50000000000) : ℚ) : ℝ) + ((9587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9587:ℚ)^(-2:ℤ) : ℝ) = ((9587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1184 : ((((113059286077 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9587 < q → q < 9601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9601).mp (by decide +kernel))) hgap
  have hprev := s2L_1183
  have hrat : ((113059286077 : ℚ) / 250000000000) ≤ ((22611856673 : ℚ) / 50000000000) + (9601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059286077 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22611856673 : ℚ) / 50000000000) : ℚ) : ℝ) + ((9601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9601:ℚ)^(-2:ℤ) : ℝ) = ((9601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1185 : ((((452237155129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9601 < q → q < 9613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9613).mp (by decide +kernel))) hgap
  have hprev := s2L_1184
  have hrat : ((452237155129 : ℚ) / 1000000000000) ≤ ((113059286077 : ℚ) / 250000000000) + (9613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237155129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059286077 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9613:ℚ)^(-2:ℤ) : ℝ) = ((9613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1186 : ((((28264822871 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9613 < q → q < 9619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9619).mp (by decide +kernel))) hgap
  have hprev := s2L_1185
  have hrat : ((28264822871 : ℚ) / 62500000000) ≤ ((452237155129 : ℚ) / 1000000000000) + (9619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264822871 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452237155129 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9619:ℚ)^(-2:ℤ) : ℝ) = ((9619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1187 : ((((226118588367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9623, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9619 < q → q < 9623 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9623).mp (by decide +kernel))) hgap
  have hprev := s2L_1186
  have hrat : ((226118588367 : ℚ) / 500000000000) ≤ ((28264822871 : ℚ) / 62500000000) + (9623:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118588367 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264822871 : ℚ) / 62500000000) : ℚ) : ℝ) + ((9623:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9623:ℚ)^(-2:ℤ) : ℝ) = ((9623:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1188 : ((((452237187519 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9629, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9623 < q → q < 9629 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9629).mp (by decide +kernel))) hgap
  have hprev := s2L_1187
  have hrat : ((452237187519 : ℚ) / 1000000000000) ≤ ((226118588367 : ℚ) / 500000000000) + (9629:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237187519 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118588367 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9629:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9629:ℚ)^(-2:ℤ) : ℝ) = ((9629:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1189 : ((((452237198299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9629 < q → q < 9631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9631).mp (by decide +kernel))) hgap
  have hprev := s2L_1188
  have hrat : ((452237198299 : ℚ) / 1000000000000) ≤ ((452237187519 : ℚ) / 1000000000000) + (9631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237198299 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237187519 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9631:ℚ)^(-2:ℤ) : ℝ) = ((9631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1190 : ((((452237209053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9643, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9631 < q → q < 9643 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9643).mp (by decide +kernel))) hgap
  have hprev := s2L_1189
  have hrat : ((452237209053 : ℚ) / 1000000000000) ≤ ((452237198299 : ℚ) / 1000000000000) + (9643:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237209053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237198299 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9643:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9643:ℚ)^(-2:ℤ) : ℝ) = ((9643:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1191 : ((((452237219793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9649, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9643 < q → q < 9649 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9649).mp (by decide +kernel))) hgap
  have hprev := s2L_1190
  have hrat : ((452237219793 : ℚ) / 1000000000000) ≤ ((452237209053 : ℚ) / 1000000000000) + (9649:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237219793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237209053 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9649:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9649:ℚ)^(-2:ℤ) : ℝ) = ((9649:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1192 : ((((452237230507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9661, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9649 < q → q < 9661 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9661).mp (by decide +kernel))) hgap
  have hprev := s2L_1191
  have hrat : ((452237230507 : ℚ) / 1000000000000) ≤ ((452237219793 : ℚ) / 1000000000000) + (9661:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237230507 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237219793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9661:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9661:ℚ)^(-2:ℤ) : ℝ) = ((9661:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1193 : ((((90447448237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9661 < q → q < 9677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9677).mp (by decide +kernel))) hgap
  have hprev := s2L_1192
  have hrat : ((90447448237 : ℚ) / 200000000000) ≤ ((452237230507 : ℚ) / 1000000000000) + (9677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447448237 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452237230507 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9677:ℚ)^(-2:ℤ) : ℝ) = ((9677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1194 : ((((452237251859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9679, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9677 < q → q < 9679 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9679).mp (by decide +kernel))) hgap
  have hprev := s2L_1193
  have hrat : ((452237251859 : ℚ) / 1000000000000) ≤ ((90447448237 : ℚ) / 200000000000) + (9679:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237251859 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447448237 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9679:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9679:ℚ)^(-2:ℤ) : ℝ) = ((9679:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1195 : ((((452237262511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9679 < q → q < 9689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9689).mp (by decide +kernel))) hgap
  have hprev := s2L_1194
  have hrat : ((452237262511 : ℚ) / 1000000000000) ≤ ((452237251859 : ℚ) / 1000000000000) + (9689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237262511 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237251859 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9689:ℚ)^(-2:ℤ) : ℝ) = ((9689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1196 : ((((90447454629 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9689 < q → q < 9697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9697).mp (by decide +kernel))) hgap
  have hprev := s2L_1195
  have hrat : ((90447454629 : ℚ) / 200000000000) ≤ ((452237262511 : ℚ) / 1000000000000) + (9697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447454629 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452237262511 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9697:ℚ)^(-2:ℤ) : ℝ) = ((9697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1197 : ((((452237283731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9697 < q → q < 9719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9719).mp (by decide +kernel))) hgap
  have hprev := s2L_1196
  have hrat : ((452237283731 : ℚ) / 1000000000000) ≤ ((90447454629 : ℚ) / 200000000000) + (9719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237283731 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447454629 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9719:ℚ)^(-2:ℤ) : ℝ) = ((9719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1198 : ((((452237294313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9719 < q → q < 9721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9721).mp (by decide +kernel))) hgap
  have hprev := s2L_1197
  have hrat : ((452237294313 : ℚ) / 1000000000000) ≤ ((452237283731 : ℚ) / 1000000000000) + (9721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237294313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237283731 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9721:ℚ)^(-2:ℤ) : ℝ) = ((9721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1199 : ((((452237304869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9721 < q → q < 9733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9733).mp (by decide +kernel))) hgap
  have hprev := s2L_1198
  have hrat : ((452237304869 : ℚ) / 1000000000000) ≤ ((452237294313 : ℚ) / 1000000000000) + (9733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237304869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237294313 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9733:ℚ)^(-2:ℤ) : ℝ) = ((9733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1200 : ((((113059328853 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9733 < q → q < 9739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9739).mp (by decide +kernel))) hgap
  have hprev := s2L_1199
  have hrat : ((113059328853 : ℚ) / 250000000000) ≤ ((452237304869 : ℚ) / 1000000000000) + (9739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059328853 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452237304869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9739:ℚ)^(-2:ℤ) : ℝ) = ((9739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1201 : ((((226118662973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9739 < q → q < 9743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9743).mp (by decide +kernel))) hgap
  have hprev := s2L_1200
  have hrat : ((226118662973 : ℚ) / 500000000000) ≤ ((113059328853 : ℚ) / 250000000000) + (9743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118662973 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059328853 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9743:ℚ)^(-2:ℤ) : ℝ) = ((9743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1202 : ((((452237336467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9749, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9743 < q → q < 9749 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9749).mp (by decide +kernel))) hgap
  have hprev := s2L_1201
  have hrat : ((452237336467 : ℚ) / 1000000000000) ≤ ((226118662973 : ℚ) / 500000000000) + (9749:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237336467 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118662973 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9749:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9749:ℚ)^(-2:ℤ) : ℝ) = ((9749:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1203 : ((((452237346949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9767, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9749 < q → q < 9767 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9767).mp (by decide +kernel))) hgap
  have hprev := s2L_1202
  have hrat : ((452237346949 : ℚ) / 1000000000000) ≤ ((452237336467 : ℚ) / 1000000000000) + (9767:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237346949 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237336467 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9767:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9767:ℚ)^(-2:ℤ) : ℝ) = ((9767:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1204 : ((((452237357427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9769, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9767 < q → q < 9769 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9769).mp (by decide +kernel))) hgap
  have hprev := s2L_1203
  have hrat : ((452237357427 : ℚ) / 1000000000000) ≤ ((452237346949 : ℚ) / 1000000000000) + (9769:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237357427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237346949 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9769:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9769:ℚ)^(-2:ℤ) : ℝ) = ((9769:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1205 : ((((452237367879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9769 < q → q < 9781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9781).mp (by decide +kernel))) hgap
  have hprev := s2L_1204
  have hrat : ((452237367879 : ℚ) / 1000000000000) ≤ ((452237357427 : ℚ) / 1000000000000) + (9781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237367879 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237357427 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9781:ℚ)^(-2:ℤ) : ℝ) = ((9781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1206 : ((((452237378319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9787, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9781 < q → q < 9787 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9787).mp (by decide +kernel))) hgap
  have hprev := s2L_1205
  have hrat : ((452237378319 : ℚ) / 1000000000000) ≤ ((452237367879 : ℚ) / 1000000000000) + (9787:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237378319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237367879 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9787:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9787:ℚ)^(-2:ℤ) : ℝ) = ((9787:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1207 : ((((361789911 : ℚ) / 800000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9787 < q → q < 9791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9791).mp (by decide +kernel))) hgap
  have hprev := s2L_1206
  have hrat : ((361789911 : ℚ) / 800000000) ≤ ((452237378319 : ℚ) / 1000000000000) + (9791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((361789911 : ℚ) / 800000000) : ℚ) : ℝ) ≤ ((((452237378319 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9791:ℚ)^(-2:ℤ) : ℝ) = ((9791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1208 : ((((90447479831 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9803, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9791 < q → q < 9803 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9803).mp (by decide +kernel))) hgap
  have hprev := s2L_1207
  have hrat : ((90447479831 : ℚ) / 200000000000) ≤ ((361789911 : ℚ) / 800000000) + (9803:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447479831 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((361789911 : ℚ) / 800000000) : ℚ) : ℝ) + ((9803:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9803:ℚ)^(-2:ℤ) : ℝ) = ((9803:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1209 : ((((452237409543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9811, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9803 < q → q < 9811 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9811).mp (by decide +kernel))) hgap
  have hprev := s2L_1208
  have hrat : ((452237409543 : ℚ) / 1000000000000) ≤ ((90447479831 : ℚ) / 200000000000) + (9811:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237409543 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447479831 : ℚ) / 200000000000) : ℚ) : ℝ) + ((9811:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9811:ℚ)^(-2:ℤ) : ℝ) = ((9811:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1210 : ((((452237419919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9817, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9811 < q → q < 9817 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9817).mp (by decide +kernel))) hgap
  have hprev := s2L_1209
  have hrat : ((452237419919 : ℚ) / 1000000000000) ≤ ((452237409543 : ℚ) / 1000000000000) + (9817:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237419919 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237409543 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9817:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9817:ℚ)^(-2:ℤ) : ℝ) = ((9817:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1211 : ((((452237430269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9817 < q → q < 9829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9829).mp (by decide +kernel))) hgap
  have hprev := s2L_1210
  have hrat : ((452237430269 : ℚ) / 1000000000000) ≤ ((452237419919 : ℚ) / 1000000000000) + (9829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237430269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237419919 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9829:ℚ)^(-2:ℤ) : ℝ) = ((9829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1212 : ((((452237440611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9829 < q → q < 9833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9833).mp (by decide +kernel))) hgap
  have hprev := s2L_1211
  have hrat : ((452237440611 : ℚ) / 1000000000000) ≤ ((452237430269 : ℚ) / 1000000000000) + (9833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237440611 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237430269 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9833:ℚ)^(-2:ℤ) : ℝ) = ((9833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1213 : ((((22611872547 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9833 < q → q < 9839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9839).mp (by decide +kernel))) hgap
  have hprev := s2L_1212
  have hrat : ((22611872547 : ℚ) / 50000000000) ≤ ((452237440611 : ℚ) / 1000000000000) + (9839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611872547 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452237440611 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9839:ℚ)^(-2:ℤ) : ℝ) = ((9839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1214 : ((((113059365311 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9851, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9839 < q → q < 9851 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9851).mp (by decide +kernel))) hgap
  have hprev := s2L_1213
  have hrat : ((113059365311 : ℚ) / 250000000000) ≤ ((22611872547 : ℚ) / 50000000000) + (9851:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059365311 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22611872547 : ℚ) / 50000000000) : ℚ) : ℝ) + ((9851:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9851:ℚ)^(-2:ℤ) : ℝ) = ((9851:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1215 : ((((28264841971 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9857, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9851 < q → q < 9857 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9857).mp (by decide +kernel))) hgap
  have hprev := s2L_1214
  have hrat : ((28264841971 : ℚ) / 62500000000) ≤ ((113059365311 : ℚ) / 250000000000) + (9857:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264841971 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((113059365311 : ℚ) / 250000000000) : ℚ) : ℝ) + ((9857:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9857:ℚ)^(-2:ℤ) : ℝ) = ((9857:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1216 : ((((14132421307 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9857 < q → q < 9859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9859).mp (by decide +kernel))) hgap
  have hprev := s2L_1215
  have hrat : ((14132421307 : ℚ) / 31250000000) ≤ ((28264841971 : ℚ) / 62500000000) + (9859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132421307 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((28264841971 : ℚ) / 62500000000) : ℚ) : ℝ) + ((9859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9859:ℚ)^(-2:ℤ) : ℝ) = ((9859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1217 : ((((452237492087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9871, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9859 < q → q < 9871 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9871).mp (by decide +kernel))) hgap
  have hprev := s2L_1216
  have hrat : ((452237492087 : ℚ) / 1000000000000) ≤ ((14132421307 : ℚ) / 31250000000) + (9871:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237492087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132421307 : ℚ) / 31250000000) : ℚ) : ℝ) + ((9871:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9871:ℚ)^(-2:ℤ) : ℝ) = ((9871:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1218 : ((((18089500093 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9871 < q → q < 9883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9883).mp (by decide +kernel))) hgap
  have hprev := s2L_1217
  have hrat : ((18089500093 : ℚ) / 40000000000) ≤ ((452237492087 : ℚ) / 1000000000000) + (9883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089500093 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452237492087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9883:ℚ)^(-2:ℤ) : ℝ) = ((9883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1219 : ((((226118756277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9883 < q → q < 9887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9887).mp (by decide +kernel))) hgap
  have hprev := s2L_1218
  have hrat : ((226118756277 : ℚ) / 500000000000) ≤ ((18089500093 : ℚ) / 40000000000) + (9887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118756277 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089500093 : ℚ) / 40000000000) : ℚ) : ℝ) + ((9887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9887:ℚ)^(-2:ℤ) : ℝ) = ((9887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1220 : ((((226118761377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9901, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9887 < q → q < 9901 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9901).mp (by decide +kernel))) hgap
  have hprev := s2L_1219
  have hrat : ((226118761377 : ℚ) / 500000000000) ≤ ((226118756277 : ℚ) / 500000000000) + (9901:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118761377 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118756277 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9901:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9901:ℚ)^(-2:ℤ) : ℝ) = ((9901:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1221 : ((((226118766471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9901 < q → q < 9907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9907).mp (by decide +kernel))) hgap
  have hprev := s2L_1220
  have hrat : ((226118766471 : ℚ) / 500000000000) ≤ ((226118761377 : ℚ) / 500000000000) + (9907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118766471 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226118761377 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9907:ℚ)^(-2:ℤ) : ℝ) = ((9907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1222 : ((((452237543097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9907 < q → q < 9923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9923).mp (by decide +kernel))) hgap
  have hprev := s2L_1221
  have hrat : ((452237543097 : ℚ) / 1000000000000) ≤ ((226118766471 : ℚ) / 500000000000) + (9923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237543097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118766471 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9923:ℚ)^(-2:ℤ) : ℝ) = ((9923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1223 : ((((11305938831 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9929, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9923 < q → q < 9929 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9929).mp (by decide +kernel))) hgap
  have hprev := s2L_1222
  have hrat : ((11305938831 : ℚ) / 25000000000) ≤ ((452237543097 : ℚ) / 1000000000000) + (9929:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305938831 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452237543097 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9929:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9929:ℚ)^(-2:ℤ) : ℝ) = ((9929:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1224 : ((((452237563379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9931, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9929 < q → q < 9931 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9931).mp (by decide +kernel))) hgap
  have hprev := s2L_1223
  have hrat : ((452237563379 : ℚ) / 1000000000000) ≤ ((11305938831 : ℚ) / 25000000000) + (9931:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237563379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11305938831 : ℚ) / 25000000000) : ℚ) : ℝ) + ((9931:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9931:ℚ)^(-2:ℤ) : ℝ) = ((9931:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1225 : ((((226118786749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9931 < q → q < 9941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9941).mp (by decide +kernel))) hgap
  have hprev := s2L_1224
  have hrat : ((226118786749 : ℚ) / 500000000000) ≤ ((452237563379 : ℚ) / 1000000000000) + (9941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118786749 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237563379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((9941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9941:ℚ)^(-2:ℤ) : ℝ) = ((9941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1226 : ((((1130593959 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9941 < q → q < 9949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9949).mp (by decide +kernel))) hgap
  have hprev := s2L_1225
  have hrat : ((1130593959 : ℚ) / 2500000000) ≤ ((226118786749 : ℚ) / 500000000000) + (9949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1130593959 : ℚ) / 2500000000) : ℚ) : ℝ) ≤ ((((226118786749 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9949:ℚ)^(-2:ℤ) : ℝ) = ((9949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1227 : ((((226118796833 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9949 < q → q < 9967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9967).mp (by decide +kernel))) hgap
  have hprev := s2L_1226
  have hrat : ((226118796833 : ℚ) / 500000000000) ≤ ((1130593959 : ℚ) / 2500000000) + (9967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118796833 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((1130593959 : ℚ) / 2500000000) : ℚ) : ℝ) + ((9967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9967:ℚ)^(-2:ℤ) : ℝ) = ((9967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1228 : ((((11305940093 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 9973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9967 < q → q < 9973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 9973).mp (by decide +kernel))) hgap
  have hprev := s2L_1227
  have hrat : ((11305940093 : ℚ) / 25000000000) ≤ ((226118796833 : ℚ) / 500000000000) + (9973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305940093 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((226118796833 : ℚ) / 500000000000) : ℚ) : ℝ) + ((9973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((9973:ℚ)^(-2:ℤ) : ℝ) = ((9973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1229 : ((((226118806853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 9973 < q → q < 10007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10007).mp (by decide +kernel))) hgap
  have hprev := s2L_1228
  have hrat : ((226118806853 : ℚ) / 500000000000) ≤ ((11305940093 : ℚ) / 25000000000) + (10007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118806853 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((11305940093 : ℚ) / 25000000000) : ℚ) : ℝ) + ((10007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10007:ℚ)^(-2:ℤ) : ℝ) = ((10007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1230 : ((((56529702961 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10007 < q → q < 10009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10009).mp (by decide +kernel))) hgap
  have hprev := s2L_1229
  have hrat : ((56529702961 : ℚ) / 125000000000) ≤ ((226118806853 : ℚ) / 500000000000) + (10009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529702961 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226118806853 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10009:ℚ)^(-2:ℤ) : ℝ) = ((10009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1231 : ((((226118816807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10009 < q → q < 10037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10037).mp (by decide +kernel))) hgap
  have hprev := s2L_1230
  have hrat : ((226118816807 : ℚ) / 500000000000) ≤ ((56529702961 : ℚ) / 125000000000) + (10037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118816807 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529702961 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10037:ℚ)^(-2:ℤ) : ℝ) = ((10037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1232 : ((((28264852721 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10039, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10037 < q → q < 10039 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10039).mp (by decide +kernel))) hgap
  have hprev := s2L_1231
  have hrat : ((28264852721 : ℚ) / 62500000000) ≤ ((226118816807 : ℚ) / 500000000000) + (10039:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264852721 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226118816807 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10039:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10039:ℚ)^(-2:ℤ) : ℝ) = ((10039:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1233 : ((((90447530683 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10061, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10039 < q → q < 10061 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10061).mp (by decide +kernel))) hgap
  have hprev := s2L_1232
  have hrat : ((90447530683 : ℚ) / 200000000000) ≤ ((28264852721 : ℚ) / 62500000000) + (10061:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447530683 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28264852721 : ℚ) / 62500000000) : ℚ) : ℝ) + ((10061:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10061:ℚ)^(-2:ℤ) : ℝ) = ((10061:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1234 : ((((226118831641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10067, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10061 < q → q < 10067 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10067).mp (by decide +kernel))) hgap
  have hprev := s2L_1233
  have hrat : ((226118831641 : ℚ) / 500000000000) ≤ ((90447530683 : ℚ) / 200000000000) + (10067:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118831641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447530683 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10067:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10067:ℚ)^(-2:ℤ) : ℝ) = ((10067:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1235 : ((((90447534629 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10067 < q → q < 10069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10069).mp (by decide +kernel))) hgap
  have hprev := s2L_1234
  have hrat : ((90447534629 : ℚ) / 200000000000) ≤ ((226118831641 : ℚ) / 500000000000) + (10069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447534629 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226118831641 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10069:ℚ)^(-2:ℤ) : ℝ) = ((10069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1236 : ((((113059420747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10079, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10069 < q → q < 10079 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10079).mp (by decide +kernel))) hgap
  have hprev := s2L_1235
  have hrat : ((113059420747 : ℚ) / 250000000000) ≤ ((90447534629 : ℚ) / 200000000000) + (10079:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059420747 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447534629 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10079:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10079:ℚ)^(-2:ℤ) : ℝ) = ((10079:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1237 : ((((56529711601 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10091, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10079 < q → q < 10091 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10091).mp (by decide +kernel))) hgap
  have hprev := s2L_1236
  have hrat : ((56529711601 : ℚ) / 125000000000) ≤ ((113059420747 : ℚ) / 250000000000) + (10091:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529711601 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113059420747 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10091:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10091:ℚ)^(-2:ℤ) : ℝ) = ((10091:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1238 : ((((14132428207 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10091 < q → q < 10093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10093).mp (by decide +kernel))) hgap
  have hprev := s2L_1237
  have hrat : ((14132428207 : ℚ) / 31250000000) ≤ ((56529711601 : ℚ) / 125000000000) + (10093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132428207 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((56529711601 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10093:ℚ)^(-2:ℤ) : ℝ) = ((10093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1239 : ((((113059428107 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10093 < q → q < 10099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10099).mp (by decide +kernel))) hgap
  have hprev := s2L_1238
  have hrat : ((113059428107 : ℚ) / 250000000000) ≤ ((14132428207 : ℚ) / 31250000000) + (10099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059428107 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((14132428207 : ℚ) / 31250000000) : ℚ) : ℝ) + ((10099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10099:ℚ)^(-2:ℤ) : ℝ) = ((10099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1240 : ((((18089508889 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10099 < q → q < 10103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10103).mp (by decide +kernel))) hgap
  have hprev := s2L_1239
  have hrat : ((18089508889 : ℚ) / 40000000000) ≤ ((113059428107 : ℚ) / 250000000000) + (10103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089508889 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((113059428107 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10103:ℚ)^(-2:ℤ) : ℝ) = ((10103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1241 : ((((226118866003 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10111, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10103 < q → q < 10111 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10111).mp (by decide +kernel))) hgap
  have hprev := s2L_1240
  have hrat : ((226118866003 : ℚ) / 500000000000) ≤ ((18089508889 : ℚ) / 40000000000) + (10111:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118866003 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089508889 : ℚ) / 40000000000) : ℚ) : ℝ) + ((10111:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10111:ℚ)^(-2:ℤ) : ℝ) = ((10111:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1242 : ((((90447548349 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10133, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10111 < q → q < 10133 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10133).mp (by decide +kernel))) hgap
  have hprev := s2L_1241
  have hrat : ((90447548349 : ℚ) / 200000000000) ≤ ((226118866003 : ℚ) / 500000000000) + (10133:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447548349 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226118866003 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10133:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10133:ℚ)^(-2:ℤ) : ℝ) = ((10133:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1243 : ((((28264859467 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10139, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10133 < q → q < 10139 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10139).mp (by decide +kernel))) hgap
  have hprev := s2L_1242
  have hrat : ((28264859467 : ℚ) / 62500000000) ≤ ((90447548349 : ℚ) / 200000000000) + (10139:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264859467 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((90447548349 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10139:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10139:ℚ)^(-2:ℤ) : ℝ) = ((10139:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1244 : ((((90447552239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10141, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10139 < q → q < 10141 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10141).mp (by decide +kernel))) hgap
  have hprev := s2L_1243
  have hrat : ((90447552239 : ℚ) / 200000000000) ≤ ((28264859467 : ℚ) / 62500000000) + (10141:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447552239 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((28264859467 : ℚ) / 62500000000) : ℚ) : ℝ) + ((10141:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10141:ℚ)^(-2:ℤ) : ℝ) = ((10141:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1245 : ((((452237770899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10141 < q → q < 10151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10151).mp (by decide +kernel))) hgap
  have hprev := s2L_1244
  have hrat : ((452237770899 : ℚ) / 1000000000000) ≤ ((90447552239 : ℚ) / 200000000000) + (10151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237770899 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447552239 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10151:ℚ)^(-2:ℤ) : ℝ) = ((10151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1246 : ((((113059445147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10151 < q → q < 10159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10159).mp (by decide +kernel))) hgap
  have hprev := s2L_1245
  have hrat : ((113059445147 : ℚ) / 250000000000) ≤ ((452237770899 : ℚ) / 1000000000000) + (10159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059445147 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452237770899 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10159:ℚ)^(-2:ℤ) : ℝ) = ((10159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1247 : ((((452237790269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10159 < q → q < 10163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10163).mp (by decide +kernel))) hgap
  have hprev := s2L_1246
  have hrat : ((452237790269 : ℚ) / 1000000000000) ≤ ((113059445147 : ℚ) / 250000000000) + (10163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237790269 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059445147 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10163:ℚ)^(-2:ℤ) : ℝ) = ((10163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1248 : ((((452237799939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10169, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10163 < q → q < 10169 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10169).mp (by decide +kernel))) hgap
  have hprev := s2L_1247
  have hrat : ((452237799939 : ℚ) / 1000000000000) ≤ ((452237790269 : ℚ) / 1000000000000) + (10169:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237799939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237790269 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10169:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10169:ℚ)^(-2:ℤ) : ℝ) = ((10169:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1249 : ((((226118904797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10169 < q → q < 10177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10177).mp (by decide +kernel))) hgap
  have hprev := s2L_1248
  have hrat : ((226118904797 : ℚ) / 500000000000) ≤ ((452237799939 : ℚ) / 1000000000000) + (10177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118904797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237799939 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10177:ℚ)^(-2:ℤ) : ℝ) = ((10177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1250 : ((((452237819241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10181, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10177 < q → q < 10181 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10181).mp (by decide +kernel))) hgap
  have hprev := s2L_1249
  have hrat : ((452237819241 : ℚ) / 1000000000000) ≤ ((226118904797 : ℚ) / 500000000000) + (10181:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237819241 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118904797 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10181:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10181:ℚ)^(-2:ℤ) : ℝ) = ((10181:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1251 : ((((90447565773 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10193, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10181 < q → q < 10193 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10193).mp (by decide +kernel))) hgap
  have hprev := s2L_1250
  have hrat : ((90447565773 : ℚ) / 200000000000) ≤ ((452237819241 : ℚ) / 1000000000000) + (10193:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447565773 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452237819241 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10193:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10193:ℚ)^(-2:ℤ) : ℝ) = ((10193:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1252 : ((((90447567691 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10193 < q → q < 10211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10211).mp (by decide +kernel))) hgap
  have hprev := s2L_1251
  have hrat : ((90447567691 : ℚ) / 200000000000) ≤ ((90447565773 : ℚ) / 200000000000) + (10211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447567691 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90447565773 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10211:ℚ)^(-2:ℤ) : ℝ) = ((10211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1253 : ((((452237848023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10223, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10211 < q → q < 10223 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10223).mp (by decide +kernel))) hgap
  have hprev := s2L_1252
  have hrat : ((452237848023 : ℚ) / 1000000000000) ≤ ((90447567691 : ℚ) / 200000000000) + (10223:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237848023 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447567691 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10223:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10223:ℚ)^(-2:ℤ) : ℝ) = ((10223:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1254 : ((((226118928777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10223 < q → q < 10243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10243).mp (by decide +kernel))) hgap
  have hprev := s2L_1253
  have hrat : ((226118928777 : ℚ) / 500000000000) ≤ ((452237848023 : ℚ) / 1000000000000) + (10243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118928777 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237848023 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10243:ℚ)^(-2:ℤ) : ℝ) = ((10243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1255 : ((((452237867077 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10247, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10243 < q → q < 10247 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10247).mp (by decide +kernel))) hgap
  have hprev := s2L_1254
  have hrat : ((452237867077 : ℚ) / 1000000000000) ≤ ((226118928777 : ℚ) / 500000000000) + (10247:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237867077 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118928777 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10247:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10247:ℚ)^(-2:ℤ) : ℝ) = ((10247:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1256 : ((((452237876589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10247 < q → q < 10253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10253).mp (by decide +kernel))) hgap
  have hprev := s2L_1255
  have hrat : ((452237876589 : ℚ) / 1000000000000) ≤ ((452237867077 : ℚ) / 1000000000000) + (10253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237876589 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237867077 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10253:ℚ)^(-2:ℤ) : ℝ) = ((10253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1257 : ((((45223788609 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10253 < q → q < 10259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10259).mp (by decide +kernel))) hgap
  have hprev := s2L_1256
  have hrat : ((45223788609 : ℚ) / 100000000000) ≤ ((452237876589 : ℚ) / 1000000000000) + (10259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223788609 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452237876589 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10259:ℚ)^(-2:ℤ) : ℝ) = ((10259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1258 : ((((56529736947 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10259 < q → q < 10267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10267).mp (by decide +kernel))) hgap
  have hprev := s2L_1257
  have hrat : ((56529736947 : ℚ) / 125000000000) ≤ ((45223788609 : ℚ) / 100000000000) + (10267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529736947 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45223788609 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10267:ℚ)^(-2:ℤ) : ℝ) = ((10267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1259 : ((((90447581011 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10271, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10267 < q → q < 10271 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10271).mp (by decide +kernel))) hgap
  have hprev := s2L_1258
  have hrat : ((90447581011 : ℚ) / 200000000000) ≤ ((56529736947 : ℚ) / 125000000000) + (10271:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447581011 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56529736947 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10271:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10271:ℚ)^(-2:ℤ) : ℝ) = ((10271:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1260 : ((((45223791453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10271 < q → q < 10273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10273).mp (by decide +kernel))) hgap
  have hprev := s2L_1259
  have hrat : ((45223791453 : ℚ) / 100000000000) ≤ ((90447581011 : ℚ) / 200000000000) + (10273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223791453 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((90447581011 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10273:ℚ)^(-2:ℤ) : ℝ) = ((10273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1261 : ((((56529740497 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10273 < q → q < 10289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10289).mp (by decide +kernel))) hgap
  have hprev := s2L_1260
  have hrat : ((56529740497 : ℚ) / 125000000000) ≤ ((45223791453 : ℚ) / 100000000000) + (10289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529740497 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((45223791453 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10289:ℚ)^(-2:ℤ) : ℝ) = ((10289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1262 : ((((2261189667 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10289 < q → q < 10301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10301).mp (by decide +kernel))) hgap
  have hprev := s2L_1261
  have hrat : ((2261189667 : ℚ) / 5000000000) ≤ ((56529740497 : ℚ) / 125000000000) + (10301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261189667 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((56529740497 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10301:ℚ)^(-2:ℤ) : ℝ) = ((10301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1263 : ((((22611897141 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10303, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10301 < q → q < 10303 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10303).mp (by decide +kernel))) hgap
  have hprev := s2L_1262
  have hrat : ((22611897141 : ℚ) / 50000000000) ≤ ((2261189667 : ℚ) / 5000000000) + (10303:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611897141 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((2261189667 : ℚ) / 5000000000) : ℚ) : ℝ) + ((10303:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10303:ℚ)^(-2:ℤ) : ℝ) = ((10303:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1264 : ((((226118976111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10303 < q → q < 10313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10313).mp (by decide +kernel))) hgap
  have hprev := s2L_1263
  have hrat : ((226118976111 : ℚ) / 500000000000) ≤ ((22611897141 : ℚ) / 50000000000) + (10313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118976111 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22611897141 : ℚ) / 50000000000) : ℚ) : ℝ) + ((10313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10313:ℚ)^(-2:ℤ) : ℝ) = ((10313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1265 : ((((452237961609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10313 < q → q < 10321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10321).mp (by decide +kernel))) hgap
  have hprev := s2L_1264
  have hrat : ((452237961609 : ℚ) / 1000000000000) ≤ ((226118976111 : ℚ) / 500000000000) + (10321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237961609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118976111 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10321:ℚ)^(-2:ℤ) : ℝ) = ((10321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1266 : ((((226118985489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10321 < q → q < 10331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10331).mp (by decide +kernel))) hgap
  have hprev := s2L_1265
  have hrat : ((226118985489 : ℚ) / 500000000000) ≤ ((452237961609 : ℚ) / 1000000000000) + (10331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226118985489 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452237961609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10331:ℚ)^(-2:ℤ) : ℝ) = ((10331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1267 : ((((452237980343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10333, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10331 < q → q < 10333 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10333).mp (by decide +kernel))) hgap
  have hprev := s2L_1266
  have hrat : ((452237980343 : ℚ) / 1000000000000) ≤ ((226118985489 : ℚ) / 500000000000) + (10333:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237980343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226118985489 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10333:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10333:ℚ)^(-2:ℤ) : ℝ) = ((10333:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1268 : ((((452237989701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10333 < q → q < 10337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10337).mp (by decide +kernel))) hgap
  have hprev := s2L_1267
  have hrat : ((452237989701 : ℚ) / 1000000000000) ≤ ((452237980343 : ℚ) / 1000000000000) + (10337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452237989701 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452237980343 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10337:ℚ)^(-2:ℤ) : ℝ) = ((10337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1269 : ((((56529749881 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10337 < q → q < 10343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10343).mp (by decide +kernel))) hgap
  have hprev := s2L_1268
  have hrat : ((56529749881 : ℚ) / 125000000000) ≤ ((452237989701 : ℚ) / 1000000000000) + (10343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529749881 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452237989701 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10343:ℚ)^(-2:ℤ) : ℝ) = ((10343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1270 : ((((45223800837 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10357, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10343 < q → q < 10357 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10357).mp (by decide +kernel))) hgap
  have hprev := s2L_1269
  have hrat : ((45223800837 : ℚ) / 100000000000) ≤ ((56529749881 : ℚ) / 125000000000) + (10357:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223800837 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((56529749881 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10357:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10357:ℚ)^(-2:ℤ) : ℝ) = ((10357:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1271 : ((((45223801767 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10357 < q → q < 10369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10369).mp (by decide +kernel))) hgap
  have hprev := s2L_1270
  have hrat : ((45223801767 : ℚ) / 100000000000) ≤ ((45223800837 : ℚ) / 100000000000) + (10369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223801767 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((45223800837 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10369:ℚ)^(-2:ℤ) : ℝ) = ((10369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1272 : ((((452238026931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10369 < q → q < 10391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10391).mp (by decide +kernel))) hgap
  have hprev := s2L_1271
  have hrat : ((452238026931 : ℚ) / 1000000000000) ≤ ((45223801767 : ℚ) / 100000000000) + (10391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238026931 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223801767 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10391:ℚ)^(-2:ℤ) : ℝ) = ((10391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1273 : ((((226119018089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10391 < q → q < 10399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10399).mp (by decide +kernel))) hgap
  have hprev := s2L_1272
  have hrat : ((226119018089 : ℚ) / 500000000000) ≤ ((452238026931 : ℚ) / 1000000000000) + (10399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119018089 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238026931 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10399:ℚ)^(-2:ℤ) : ℝ) = ((10399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1274 : ((((3617904363 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10427, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10399 < q → q < 10427 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10427).mp (by decide +kernel))) hgap
  have hprev := s2L_1273
  have hrat : ((3617904363 : ℚ) / 8000000000) ≤ ((226119018089 : ℚ) / 500000000000) + (10427:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3617904363 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((226119018089 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10427:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10427:ℚ)^(-2:ℤ) : ℝ) = ((10427:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1275 : ((((452238054569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10429, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10427 < q → q < 10429 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10429).mp (by decide +kernel))) hgap
  have hprev := s2L_1274
  have hrat : ((452238054569 : ℚ) / 1000000000000) ≤ ((3617904363 : ℚ) / 8000000000) + (10429:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238054569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3617904363 : ℚ) / 8000000000) : ℚ) : ℝ) + ((10429:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10429:ℚ)^(-2:ℤ) : ℝ) = ((10429:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1276 : ((((113059515939 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10429 < q → q < 10433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10433).mp (by decide +kernel))) hgap
  have hprev := s2L_1275
  have hrat : ((113059515939 : ℚ) / 250000000000) ≤ ((452238054569 : ℚ) / 1000000000000) + (10433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059515939 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452238054569 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10433:ℚ)^(-2:ℤ) : ℝ) = ((10433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1277 : ((((113059518227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10453, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10433 < q → q < 10453 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10453).mp (by decide +kernel))) hgap
  have hprev := s2L_1276
  have hrat : ((113059518227 : ℚ) / 250000000000) ≤ ((113059515939 : ℚ) / 250000000000) + (10453:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059518227 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113059515939 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10453:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10453:ℚ)^(-2:ℤ) : ℝ) = ((10453:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1278 : ((((452238082053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10453 < q → q < 10457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10457).mp (by decide +kernel))) hgap
  have hprev := s2L_1277
  have hrat : ((452238082053 : ℚ) / 1000000000000) ≤ ((113059518227 : ℚ) / 250000000000) + (10457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238082053 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059518227 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10457:ℚ)^(-2:ℤ) : ℝ) = ((10457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1279 : ((((226119045597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10459, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10457 < q → q < 10459 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10459).mp (by decide +kernel))) hgap
  have hprev := s2L_1278
  have hrat : ((226119045597 : ℚ) / 500000000000) ≤ ((452238082053 : ℚ) / 1000000000000) + (10459:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119045597 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238082053 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10459:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10459:ℚ)^(-2:ℤ) : ℝ) = ((10459:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1280 : ((((56529762541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10459 < q → q < 10463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10463).mp (by decide +kernel))) hgap
  have hprev := s2L_1279
  have hrat : ((56529762541 : ℚ) / 125000000000) ≤ ((226119045597 : ℚ) / 500000000000) + (10463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529762541 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226119045597 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10463:ℚ)^(-2:ℤ) : ℝ) = ((10463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1281 : ((((226119054719 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10463 < q → q < 10477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10477).mp (by decide +kernel))) hgap
  have hprev := s2L_1280
  have hrat : ((226119054719 : ℚ) / 500000000000) ≤ ((56529762541 : ℚ) / 125000000000) + (10477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119054719 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529762541 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10477:ℚ)^(-2:ℤ) : ℝ) = ((10477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1282 : ((((45223811853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10477 < q → q < 10487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10487).mp (by decide +kernel))) hgap
  have hprev := s2L_1281
  have hrat : ((45223811853 : ℚ) / 100000000000) ≤ ((226119054719 : ℚ) / 500000000000) + (10487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223811853 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226119054719 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10487:ℚ)^(-2:ℤ) : ℝ) = ((10487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1283 : ((((226119063801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10487 < q → q < 10499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10499).mp (by decide +kernel))) hgap
  have hprev := s2L_1282
  have hrat : ((226119063801 : ℚ) / 500000000000) ≤ ((45223811853 : ℚ) / 100000000000) + (10499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119063801 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45223811853 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10499:ℚ)^(-2:ℤ) : ℝ) = ((10499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1284 : ((((45223813667 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10501, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10499 < q → q < 10501 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10501).mp (by decide +kernel))) hgap
  have hprev := s2L_1283
  have hrat : ((45223813667 : ℚ) / 100000000000) ≤ ((226119063801 : ℚ) / 500000000000) + (10501:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223813667 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226119063801 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10501:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10501:ℚ)^(-2:ℤ) : ℝ) = ((10501:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1285 : ((((452238145717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10501 < q → q < 10513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10513).mp (by decide +kernel))) hgap
  have hprev := s2L_1284
  have hrat : ((452238145717 : ℚ) / 1000000000000) ≤ ((45223813667 : ℚ) / 100000000000) + (10513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238145717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223813667 : ℚ) / 100000000000) : ℚ) : ℝ) + ((10513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10513:ℚ)^(-2:ℤ) : ℝ) = ((10513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1286 : ((((452238154737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10529, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10513 < q → q < 10529 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10529).mp (by decide +kernel))) hgap
  have hprev := s2L_1285
  have hrat : ((452238154737 : ℚ) / 1000000000000) ≤ ((452238145717 : ℚ) / 1000000000000) + (10529:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238154737 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238145717 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10529:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10529:ℚ)^(-2:ℤ) : ℝ) = ((10529:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1287 : ((((452238163753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10531, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10529 < q → q < 10531 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10531).mp (by decide +kernel))) hgap
  have hprev := s2L_1286
  have hrat : ((452238163753 : ℚ) / 1000000000000) ≤ ((452238154737 : ℚ) / 1000000000000) + (10531:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238163753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238154737 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10531:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10531:ℚ)^(-2:ℤ) : ℝ) = ((10531:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1288 : ((((226119086361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10559, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10531 < q → q < 10559 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10559).mp (by decide +kernel))) hgap
  have hprev := s2L_1287
  have hrat : ((226119086361 : ℚ) / 500000000000) ≤ ((452238163753 : ℚ) / 1000000000000) + (10559:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119086361 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238163753 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10559:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10559:ℚ)^(-2:ℤ) : ℝ) = ((10559:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1289 : ((((452238181677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10567, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10559 < q → q < 10567 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10567).mp (by decide +kernel))) hgap
  have hprev := s2L_1288
  have hrat : ((452238181677 : ℚ) / 1000000000000) ≤ ((226119086361 : ℚ) / 500000000000) + (10567:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238181677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119086361 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10567:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10567:ℚ)^(-2:ℤ) : ℝ) = ((10567:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1290 : ((((90447638119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10589, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10567 < q → q < 10589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10589).mp (by decide +kernel))) hgap
  have hprev := s2L_1289
  have hrat : ((90447638119 : ℚ) / 200000000000) ≤ ((452238181677 : ℚ) / 1000000000000) + (10589:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447638119 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452238181677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10589:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10589:ℚ)^(-2:ℤ) : ℝ) = ((10589:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1291 : ((((904476399 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10589 < q → q < 10597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10597).mp (by decide +kernel))) hgap
  have hprev := s2L_1290
  have hrat : ((904476399 : ℚ) / 2000000000) ≤ ((90447638119 : ℚ) / 200000000000) + (10597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904476399 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((90447638119 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10597:ℚ)^(-2:ℤ) : ℝ) = ((10597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1292 : ((((226119104199 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10597 < q → q < 10601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10601).mp (by decide +kernel))) hgap
  have hprev := s2L_1291
  have hrat : ((226119104199 : ℚ) / 500000000000) ≤ ((904476399 : ℚ) / 2000000000) + (10601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119104199 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((904476399 : ℚ) / 2000000000) : ℚ) : ℝ) + ((10601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10601:ℚ)^(-2:ℤ) : ℝ) = ((10601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1293 : ((((226119108643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10607, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10601 < q → q < 10607 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10607).mp (by decide +kernel))) hgap
  have hprev := s2L_1292
  have hrat : ((226119108643 : ℚ) / 500000000000) ≤ ((226119104199 : ℚ) / 500000000000) + (10607:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119108643 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119104199 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10607:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10607:ℚ)^(-2:ℤ) : ℝ) = ((10607:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1294 : ((((113059556541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10607 < q → q < 10613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10613).mp (by decide +kernel))) hgap
  have hprev := s2L_1293
  have hrat : ((113059556541 : ℚ) / 250000000000) ≤ ((226119108643 : ℚ) / 500000000000) + (10613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059556541 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119108643 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10613:ℚ)^(-2:ℤ) : ℝ) = ((10613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1295 : ((((226119117509 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10627, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10613 < q → q < 10627 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10627).mp (by decide +kernel))) hgap
  have hprev := s2L_1294
  have hrat : ((226119117509 : ℚ) / 500000000000) ≤ ((113059556541 : ℚ) / 250000000000) + (10627:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119117509 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059556541 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10627:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10627:ℚ)^(-2:ℤ) : ℝ) = ((10627:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1296 : ((((226119121933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10631, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10627 < q → q < 10631 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10631).mp (by decide +kernel))) hgap
  have hprev := s2L_1295
  have hrat : ((226119121933 : ℚ) / 500000000000) ≤ ((226119117509 : ℚ) / 500000000000) + (10631:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119121933 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119117509 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10631:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10631:ℚ)^(-2:ℤ) : ℝ) = ((10631:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1297 : ((((4522382527 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10639, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10631 < q → q < 10639 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10639).mp (by decide +kernel))) hgap
  have hprev := s2L_1296
  have hrat : ((4522382527 : ℚ) / 10000000000) ≤ ((226119121933 : ℚ) / 500000000000) + (10639:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522382527 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226119121933 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10639:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10639:ℚ)^(-2:ℤ) : ℝ) = ((10639:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1298 : ((((226119130757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10651, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10639 < q → q < 10651 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10651).mp (by decide +kernel))) hgap
  have hprev := s2L_1297
  have hrat : ((226119130757 : ℚ) / 500000000000) ≤ ((4522382527 : ℚ) / 10000000000) + (10651:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119130757 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522382527 : ℚ) / 10000000000) : ℚ) : ℝ) + ((10651:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10651:ℚ)^(-2:ℤ) : ℝ) = ((10651:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1299 : ((((452238270319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10651 < q → q < 10657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10657).mp (by decide +kernel))) hgap
  have hprev := s2L_1298
  have hrat : ((452238270319 : ℚ) / 1000000000000) ≤ ((226119130757 : ℚ) / 500000000000) + (10657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238270319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119130757 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10657:ℚ)^(-2:ℤ) : ℝ) = ((10657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1300 : ((((226119139557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10663, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10657 < q → q < 10663 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10663).mp (by decide +kernel))) hgap
  have hprev := s2L_1299
  have hrat : ((226119139557 : ℚ) / 500000000000) ≤ ((452238270319 : ℚ) / 1000000000000) + (10663:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119139557 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238270319 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10663:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10663:ℚ)^(-2:ℤ) : ℝ) = ((10663:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1301 : ((((226119143951 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10667, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10663 < q → q < 10667 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10667).mp (by decide +kernel))) hgap
  have hprev := s2L_1300
  have hrat : ((226119143951 : ℚ) / 500000000000) ≤ ((226119139557 : ℚ) / 500000000000) + (10667:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119143951 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119139557 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10667:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10667:ℚ)^(-2:ℤ) : ℝ) = ((10667:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1302 : ((((452238296657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10687, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10667 < q → q < 10687 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10687).mp (by decide +kernel))) hgap
  have hprev := s2L_1301
  have hrat : ((452238296657 : ℚ) / 1000000000000) ≤ ((226119143951 : ℚ) / 500000000000) + (10687:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238296657 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119143951 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10687:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10687:ℚ)^(-2:ℤ) : ℝ) = ((10687:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1303 : ((((226119152703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10691, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10687 < q → q < 10691 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10691).mp (by decide +kernel))) hgap
  have hprev := s2L_1302
  have hrat : ((226119152703 : ℚ) / 500000000000) ≤ ((452238296657 : ℚ) / 1000000000000) + (10691:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119152703 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238296657 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10691:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10691:ℚ)^(-2:ℤ) : ℝ) = ((10691:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1304 : ((((3617906513 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10709, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10691 < q → q < 10709 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10709).mp (by decide +kernel))) hgap
  have hprev := s2L_1303
  have hrat : ((3617906513 : ℚ) / 8000000000) ≤ ((226119152703 : ℚ) / 500000000000) + (10709:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3617906513 : ℚ) / 8000000000) : ℚ) : ℝ) ≤ ((((226119152703 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10709:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10709:ℚ)^(-2:ℤ) : ℝ) = ((10709:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1305 : ((((452238322841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10711, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10709 < q → q < 10711 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10711).mp (by decide +kernel))) hgap
  have hprev := s2L_1304
  have hrat : ((452238322841 : ℚ) / 1000000000000) ≤ ((3617906513 : ℚ) / 8000000000) + (10711:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238322841 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((3617906513 : ℚ) / 8000000000) : ℚ) : ℝ) + ((10711:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10711:ℚ)^(-2:ℤ) : ℝ) = ((10711:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1306 : ((((452238331537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10723, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10711 < q → q < 10723 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10723).mp (by decide +kernel))) hgap
  have hprev := s2L_1305
  have hrat : ((452238331537 : ℚ) / 1000000000000) ≤ ((452238322841 : ℚ) / 1000000000000) + (10723:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238331537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238322841 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10723:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10723:ℚ)^(-2:ℤ) : ℝ) = ((10723:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1307 : ((((3533112033 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10729, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10723 < q → q < 10729 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10729).mp (by decide +kernel))) hgap
  have hprev := s2L_1306
  have hrat : ((3533112033 : ℚ) / 7812500000) ≤ ((452238331537 : ℚ) / 1000000000000) + (10729:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((3533112033 : ℚ) / 7812500000) : ℚ) : ℝ) ≤ ((((452238331537 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10729:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10729:ℚ)^(-2:ℤ) : ℝ) = ((10729:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1308 : ((((56529793613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10733, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10729 < q → q < 10733 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10733).mp (by decide +kernel))) hgap
  have hprev := s2L_1307
  have hrat : ((56529793613 : ℚ) / 125000000000) ≤ ((3533112033 : ℚ) / 7812500000) + (10733:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529793613 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((3533112033 : ℚ) / 7812500000) : ℚ) : ℝ) + ((10733:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10733:ℚ)^(-2:ℤ) : ℝ) = ((10733:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1309 : ((((18089534303 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10733 < q → q < 10739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10739).mp (by decide +kernel))) hgap
  have hprev := s2L_1308
  have hrat : ((18089534303 : ℚ) / 40000000000) ≤ ((56529793613 : ℚ) / 125000000000) + (10739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089534303 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((56529793613 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10739:ℚ)^(-2:ℤ) : ℝ) = ((10739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1310 : ((((452238366223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10753, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10739 < q → q < 10753 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10753).mp (by decide +kernel))) hgap
  have hprev := s2L_1309
  have hrat : ((452238366223 : ℚ) / 1000000000000) ≤ ((18089534303 : ℚ) / 40000000000) + (10753:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238366223 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089534303 : ℚ) / 40000000000) : ℚ) : ℝ) + ((10753:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10753:ℚ)^(-2:ℤ) : ℝ) = ((10753:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1311 : ((((226119187421 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10771, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10753 < q → q < 10771 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10771).mp (by decide +kernel))) hgap
  have hprev := s2L_1310
  have hrat : ((226119187421 : ℚ) / 500000000000) ≤ ((452238366223 : ℚ) / 1000000000000) + (10771:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119187421 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238366223 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10771:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10771:ℚ)^(-2:ℤ) : ℝ) = ((10771:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1312 : ((((90447676689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10771 < q → q < 10781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10781).mp (by decide +kernel))) hgap
  have hprev := s2L_1311
  have hrat : ((90447676689 : ℚ) / 200000000000) ≤ ((226119187421 : ℚ) / 500000000000) + (10781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447676689 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119187421 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10781:ℚ)^(-2:ℤ) : ℝ) = ((10781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1313 : ((((90447678407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10781 < q → q < 10789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10789).mp (by decide +kernel))) hgap
  have hprev := s2L_1312
  have hrat : ((90447678407 : ℚ) / 200000000000) ≤ ((90447676689 : ℚ) / 200000000000) + (10789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447678407 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90447676689 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10789:ℚ)^(-2:ℤ) : ℝ) = ((10789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1314 : ((((452238400609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10789 < q → q < 10799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10799).mp (by decide +kernel))) hgap
  have hprev := s2L_1313
  have hrat : ((452238400609 : ℚ) / 1000000000000) ≤ ((90447678407 : ℚ) / 200000000000) + (10799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238400609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447678407 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10799:ℚ)^(-2:ℤ) : ℝ) = ((10799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1315 : ((((452238409133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10799 < q → q < 10831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10831).mp (by decide +kernel))) hgap
  have hprev := s2L_1314
  have hrat : ((452238409133 : ℚ) / 1000000000000) ≤ ((452238400609 : ℚ) / 1000000000000) + (10831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238409133 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238400609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10831:ℚ)^(-2:ℤ) : ℝ) = ((10831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1316 : ((((452238417647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10837, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10831 < q → q < 10837 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10837).mp (by decide +kernel))) hgap
  have hprev := s2L_1315
  have hrat : ((452238417647 : ℚ) / 1000000000000) ≤ ((452238409133 : ℚ) / 1000000000000) + (10837:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238417647 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238409133 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10837:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10837:ℚ)^(-2:ℤ) : ℝ) = ((10837:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1317 : ((((226119213073 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10847, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10837 < q → q < 10847 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10847).mp (by decide +kernel))) hgap
  have hprev := s2L_1316
  have hrat : ((226119213073 : ℚ) / 500000000000) ≤ ((452238417647 : ℚ) / 1000000000000) + (10847:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119213073 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238417647 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10847:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10847:ℚ)^(-2:ℤ) : ℝ) = ((10847:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1318 : ((((90447686927 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10847 < q → q < 10853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10853).mp (by decide +kernel))) hgap
  have hprev := s2L_1317
  have hrat : ((90447686927 : ℚ) / 200000000000) ≤ ((226119213073 : ℚ) / 500000000000) + (10853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447686927 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119213073 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10853:ℚ)^(-2:ℤ) : ℝ) = ((10853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1319 : ((((90447688623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10859, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10853 < q → q < 10859 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10859).mp (by decide +kernel))) hgap
  have hprev := s2L_1318
  have hrat : ((90447688623 : ℚ) / 200000000000) ≤ ((90447686927 : ℚ) / 200000000000) + (10859:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447688623 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90447686927 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10859:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10859:ℚ)^(-2:ℤ) : ℝ) = ((10859:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1320 : ((((56529806449 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10861, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10859 < q → q < 10861 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10861).mp (by decide +kernel))) hgap
  have hprev := s2L_1319
  have hrat : ((56529806449 : ℚ) / 125000000000) ≤ ((90447688623 : ℚ) / 200000000000) + (10861:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529806449 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90447688623 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10861:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10861:ℚ)^(-2:ℤ) : ℝ) = ((10861:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1321 : ((((452238460059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10861 < q → q < 10867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10867).mp (by decide +kernel))) hgap
  have hprev := s2L_1320
  have hrat : ((452238460059 : ℚ) / 1000000000000) ≤ ((56529806449 : ℚ) / 125000000000) + (10867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238460059 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529806449 : ℚ) / 125000000000) : ℚ) : ℝ) + ((10867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10867:ℚ)^(-2:ℤ) : ℝ) = ((10867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1322 : ((((226119234251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10883, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10867 < q → q < 10883 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10883).mp (by decide +kernel))) hgap
  have hprev := s2L_1321
  have hrat : ((226119234251 : ℚ) / 500000000000) ≤ ((452238460059 : ℚ) / 1000000000000) + (10883:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119234251 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238460059 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10883:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10883:ℚ)^(-2:ℤ) : ℝ) = ((10883:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1323 : ((((90447695387 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10883 < q → q < 10889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10889).mp (by decide +kernel))) hgap
  have hprev := s2L_1322
  have hrat : ((90447695387 : ℚ) / 200000000000) ≤ ((226119234251 : ℚ) / 500000000000) + (10889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447695387 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119234251 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10889:ℚ)^(-2:ℤ) : ℝ) = ((10889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1324 : ((((90447697073 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10891, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10889 < q → q < 10891 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10891).mp (by decide +kernel))) hgap
  have hprev := s2L_1323
  have hrat : ((90447697073 : ℚ) / 200000000000) ≤ ((90447695387 : ℚ) / 200000000000) + (10891:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447697073 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((90447695387 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10891:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10891:ℚ)^(-2:ℤ) : ℝ) = ((10891:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1325 : ((((452238493777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10891 < q → q < 10903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10903).mp (by decide +kernel))) hgap
  have hprev := s2L_1324
  have hrat : ((452238493777 : ℚ) / 1000000000000) ≤ ((90447697073 : ℚ) / 200000000000) + (10903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238493777 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447697073 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10903:ℚ)^(-2:ℤ) : ℝ) = ((10903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1326 : ((((452238502179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10903 < q → q < 10909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10909).mp (by decide +kernel))) hgap
  have hprev := s2L_1325
  have hrat : ((452238502179 : ℚ) / 1000000000000) ≤ ((452238493777 : ℚ) / 1000000000000) + (10909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238502179 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238493777 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10909:ℚ)^(-2:ℤ) : ℝ) = ((10909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1327 : ((((226119255269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10937, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10909 < q → q < 10937 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10937).mp (by decide +kernel))) hgap
  have hprev := s2L_1326
  have hrat : ((226119255269 : ℚ) / 500000000000) ≤ ((452238502179 : ℚ) / 1000000000000) + (10937:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119255269 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238502179 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10937:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10937:ℚ)^(-2:ℤ) : ℝ) = ((10937:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1328 : ((((226119259447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10937 < q → q < 10939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10939).mp (by decide +kernel))) hgap
  have hprev := s2L_1327
  have hrat : ((226119259447 : ℚ) / 500000000000) ≤ ((226119255269 : ℚ) / 500000000000) + (10939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119259447 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119255269 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10939:ℚ)^(-2:ℤ) : ℝ) = ((10939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1329 : ((((90447705447 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10949, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10939 < q → q < 10949 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10949).mp (by decide +kernel))) hgap
  have hprev := s2L_1328
  have hrat : ((90447705447 : ℚ) / 200000000000) ≤ ((226119259447 : ℚ) / 500000000000) + (10949:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447705447 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119259447 : ℚ) / 500000000000) : ℚ) : ℝ) + ((10949:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10949:ℚ)^(-2:ℤ) : ℝ) = ((10949:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1330 : ((((113059633891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10957, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10949 < q → q < 10957 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10957).mp (by decide +kernel))) hgap
  have hprev := s2L_1329
  have hrat : ((113059633891 : ℚ) / 250000000000) ≤ ((90447705447 : ℚ) / 200000000000) + (10957:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059633891 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447705447 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10957:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10957:ℚ)^(-2:ℤ) : ℝ) = ((10957:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1331 : ((((452238543869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10957 < q → q < 10973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10973).mp (by decide +kernel))) hgap
  have hprev := s2L_1330
  have hrat : ((452238543869 : ℚ) / 1000000000000) ≤ ((113059633891 : ℚ) / 250000000000) + (10973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238543869 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059633891 : ℚ) / 250000000000) : ℚ) : ℝ) + ((10973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10973:ℚ)^(-2:ℤ) : ℝ) = ((10973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1332 : ((((90447710433 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10973 < q → q < 10979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10979).mp (by decide +kernel))) hgap
  have hprev := s2L_1331
  have hrat : ((90447710433 : ℚ) / 200000000000) ≤ ((452238543869 : ℚ) / 1000000000000) + (10979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447710433 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452238543869 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10979:ℚ)^(-2:ℤ) : ℝ) = ((10979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1333 : ((((452238560449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10979 < q → q < 10987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10987).mp (by decide +kernel))) hgap
  have hprev := s2L_1332
  have hrat : ((452238560449 : ℚ) / 1000000000000) ≤ ((90447710433 : ℚ) / 200000000000) + (10987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238560449 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447710433 : ℚ) / 200000000000) : ℚ) : ℝ) + ((10987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10987:ℚ)^(-2:ℤ) : ℝ) = ((10987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1334 : ((((452238568723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 10993, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10987 < q → q < 10993 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 10993).mp (by decide +kernel))) hgap
  have hprev := s2L_1333
  have hrat : ((452238568723 : ℚ) / 1000000000000) ≤ ((452238560449 : ℚ) / 1000000000000) + (10993:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238568723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238560449 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((10993:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((10993:ℚ)^(-2:ℤ) : ℝ) = ((10993:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1335 : ((((226119288491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 10993 < q → q < 11003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11003).mp (by decide +kernel))) hgap
  have hprev := s2L_1334
  have hrat : ((226119288491 : ℚ) / 500000000000) ≤ ((452238568723 : ℚ) / 1000000000000) + (11003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119288491 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238568723 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11003:ℚ)^(-2:ℤ) : ℝ) = ((11003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1336 : ((((226119292603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11027, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11003 < q → q < 11027 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11027).mp (by decide +kernel))) hgap
  have hprev := s2L_1335
  have hrat : ((226119292603 : ℚ) / 500000000000) ≤ ((226119288491 : ℚ) / 500000000000) + (11027:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119292603 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119288491 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11027:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11027:ℚ)^(-2:ℤ) : ℝ) = ((11027:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1337 : ((((2261192967 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11047, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11027 < q → q < 11047 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11047).mp (by decide +kernel))) hgap
  have hprev := s2L_1336
  have hrat : ((2261192967 : ℚ) / 5000000000) ≤ ((226119292603 : ℚ) / 500000000000) + (11047:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2261192967 : ℚ) / 5000000000) : ℚ) : ℝ) ≤ ((((226119292603 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11047:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11047:ℚ)^(-2:ℤ) : ℝ) = ((11047:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1338 : ((((452238601579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11057, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11047 < q → q < 11057 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11057).mp (by decide +kernel))) hgap
  have hprev := s2L_1337
  have hrat : ((452238601579 : ℚ) / 1000000000000) ≤ ((2261192967 : ℚ) / 5000000000) + (11057:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238601579 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2261192967 : ℚ) / 5000000000) : ℚ) : ℝ) + ((11057:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11057:ℚ)^(-2:ℤ) : ℝ) = ((11057:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1339 : ((((90447721951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11059, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11057 < q → q < 11059 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11059).mp (by decide +kernel))) hgap
  have hprev := s2L_1338
  have hrat : ((90447721951 : ℚ) / 200000000000) ≤ ((452238601579 : ℚ) / 1000000000000) + (11059:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447721951 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452238601579 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11059:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11059:ℚ)^(-2:ℤ) : ℝ) = ((11059:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1340 : ((((113059654479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11069, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11059 < q → q < 11069 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11069).mp (by decide +kernel))) hgap
  have hprev := s2L_1339
  have hrat : ((113059654479 : ℚ) / 250000000000) ≤ ((90447721951 : ℚ) / 200000000000) + (11069:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059654479 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447721951 : ℚ) / 200000000000) : ℚ) : ℝ) + ((11069:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11069:ℚ)^(-2:ℤ) : ℝ) = ((11069:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1341 : ((((226119313037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11069 < q → q < 11071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11071).mp (by decide +kernel))) hgap
  have hprev := s2L_1340
  have hrat : ((226119313037 : ℚ) / 500000000000) ≤ ((113059654479 : ℚ) / 250000000000) + (11071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119313037 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059654479 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11071:ℚ)^(-2:ℤ) : ℝ) = ((11071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1342 : ((((90447726843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11083, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11071 < q → q < 11083 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11083).mp (by decide +kernel))) hgap
  have hprev := s2L_1341
  have hrat : ((90447726843 : ℚ) / 200000000000) ≤ ((226119313037 : ℚ) / 500000000000) + (11083:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447726843 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119313037 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11083:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11083:ℚ)^(-2:ℤ) : ℝ) = ((11083:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1343 : ((((9044772847 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11087, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11083 < q → q < 11087 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11087).mp (by decide +kernel))) hgap
  have hprev := s2L_1342
  have hrat : ((9044772847 : ℚ) / 20000000000) ≤ ((90447726843 : ℚ) / 200000000000) + (11087:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044772847 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((90447726843 : ℚ) / 200000000000) : ℚ) : ℝ) + ((11087:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11087:ℚ)^(-2:ℤ) : ℝ) = ((11087:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1344 : ((((113059662619 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11087 < q → q < 11093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11093).mp (by decide +kernel))) hgap
  have hprev := s2L_1343
  have hrat : ((113059662619 : ℚ) / 250000000000) ≤ ((9044772847 : ℚ) / 20000000000) + (11093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059662619 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9044772847 : ℚ) / 20000000000) : ℚ) : ℝ) + ((11093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11093:ℚ)^(-2:ℤ) : ℝ) = ((11093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1345 : ((((452238658573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11093 < q → q < 11113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11113).mp (by decide +kernel))) hgap
  have hprev := s2L_1344
  have hrat : ((452238658573 : ℚ) / 1000000000000) ≤ ((113059662619 : ℚ) / 250000000000) + (11113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238658573 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059662619 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11113:ℚ)^(-2:ℤ) : ℝ) = ((11113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1346 : ((((56529833333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11117, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11113 < q → q < 11117 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11117).mp (by decide +kernel))) hgap
  have hprev := s2L_1345
  have hrat : ((56529833333 : ℚ) / 125000000000) ≤ ((452238658573 : ℚ) / 1000000000000) + (11117:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529833333 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452238658573 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11117:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11117:ℚ)^(-2:ℤ) : ℝ) = ((11117:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1347 : ((((7066229293 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11117 < q → q < 11119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11119).mp (by decide +kernel))) hgap
  have hprev := s2L_1346
  have hrat : ((7066229293 : ℚ) / 15625000000) ≤ ((56529833333 : ℚ) / 125000000000) + (11119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066229293 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((56529833333 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11119:ℚ)^(-2:ℤ) : ℝ) = ((11119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1348 : ((((452238682823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11131, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11119 < q → q < 11131 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11131).mp (by decide +kernel))) hgap
  have hprev := s2L_1347
  have hrat : ((452238682823 : ℚ) / 1000000000000) ≤ ((7066229293 : ℚ) / 15625000000) + (11131:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238682823 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066229293 : ℚ) / 15625000000) : ℚ) : ℝ) + ((11131:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11131:ℚ)^(-2:ℤ) : ℝ) = ((11131:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1349 : ((((113059672717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11131 < q → q < 11149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11149).mp (by decide +kernel))) hgap
  have hprev := s2L_1348
  have hrat : ((113059672717 : ℚ) / 250000000000) ≤ ((452238682823 : ℚ) / 1000000000000) + (11149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059672717 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452238682823 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11149:ℚ)^(-2:ℤ) : ℝ) = ((11149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1350 : ((((226119349449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11149 < q → q < 11159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11159).mp (by decide +kernel))) hgap
  have hprev := s2L_1349
  have hrat : ((226119349449 : ℚ) / 500000000000) ≤ ((113059672717 : ℚ) / 250000000000) + (11159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119349449 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059672717 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11159:ℚ)^(-2:ℤ) : ℝ) = ((11159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1351 : ((((18089548277 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11159 < q → q < 11161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11161).mp (by decide +kernel))) hgap
  have hprev := s2L_1350
  have hrat : ((18089548277 : ℚ) / 40000000000) ≤ ((226119349449 : ℚ) / 500000000000) + (11161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089548277 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226119349449 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11161:ℚ)^(-2:ℤ) : ℝ) = ((11161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1352 : ((((226119357469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11161 < q → q < 11171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11171).mp (by decide +kernel))) hgap
  have hprev := s2L_1351
  have hrat : ((226119357469 : ℚ) / 500000000000) ≤ ((18089548277 : ℚ) / 40000000000) + (11171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119357469 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089548277 : ℚ) / 40000000000) : ℚ) : ℝ) + ((11171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11171:ℚ)^(-2:ℤ) : ℝ) = ((11171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1353 : ((((113059680737 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11173, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11171 < q → q < 11173 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11173).mp (by decide +kernel))) hgap
  have hprev := s2L_1352
  have hrat : ((113059680737 : ℚ) / 250000000000) ≤ ((226119357469 : ℚ) / 500000000000) + (11173:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059680737 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119357469 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11173:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11173:ℚ)^(-2:ℤ) : ℝ) = ((11173:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1354 : ((((56529841369 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11173 < q → q < 11177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11177).mp (by decide +kernel))) hgap
  have hprev := s2L_1353
  have hrat : ((56529841369 : ℚ) / 125000000000) ≤ ((113059680737 : ℚ) / 250000000000) + (11177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529841369 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113059680737 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11177:ℚ)^(-2:ℤ) : ℝ) = ((11177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1355 : ((((28264921183 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11177 < q → q < 11197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11197).mp (by decide +kernel))) hgap
  have hprev := s2L_1354
  have hrat : ((28264921183 : ℚ) / 62500000000) ≤ ((56529841369 : ℚ) / 125000000000) + (11197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264921183 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((56529841369 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11197:ℚ)^(-2:ℤ) : ℝ) = ((11197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1356 : ((((452238746881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11213, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11197 < q → q < 11213 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11213).mp (by decide +kernel))) hgap
  have hprev := s2L_1355
  have hrat : ((452238746881 : ℚ) / 1000000000000) ≤ ((28264921183 : ℚ) / 62500000000) + (11213:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238746881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((28264921183 : ℚ) / 62500000000) : ℚ) : ℝ) + ((11213:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11213:ℚ)^(-2:ℤ) : ℝ) = ((11213:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1357 : ((((452238754797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11213 < q → q < 11239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11239).mp (by decide +kernel))) hgap
  have hprev := s2L_1356
  have hrat : ((452238754797 : ℚ) / 1000000000000) ≤ ((452238746881 : ℚ) / 1000000000000) + (11239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238754797 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238746881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11239:ℚ)^(-2:ℤ) : ℝ) = ((11239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1358 : ((((113059690677 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11243, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11239 < q → q < 11243 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11243).mp (by decide +kernel))) hgap
  have hprev := s2L_1357
  have hrat : ((113059690677 : ℚ) / 250000000000) ≤ ((452238754797 : ℚ) / 1000000000000) + (11243:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059690677 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452238754797 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11243:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11243:ℚ)^(-2:ℤ) : ℝ) = ((11243:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1359 : ((((452238770607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11243 < q → q < 11251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11251).mp (by decide +kernel))) hgap
  have hprev := s2L_1358
  have hrat : ((452238770607 : ℚ) / 1000000000000) ≤ ((113059690677 : ℚ) / 250000000000) + (11251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238770607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059690677 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11251:ℚ)^(-2:ℤ) : ℝ) = ((11251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1360 : ((((226119389249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11257, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11251 < q → q < 11257 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11257).mp (by decide +kernel))) hgap
  have hprev := s2L_1359
  have hrat : ((226119389249 : ℚ) / 500000000000) ≤ ((452238770607 : ℚ) / 1000000000000) + (11257:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119389249 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238770607 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11257:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11257:ℚ)^(-2:ℤ) : ℝ) = ((11257:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1361 : ((((452238786383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11261, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11257 < q → q < 11261 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11261).mp (by decide +kernel))) hgap
  have hprev := s2L_1360
  have hrat : ((452238786383 : ℚ) / 1000000000000) ≤ ((226119389249 : ℚ) / 500000000000) + (11261:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238786383 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119389249 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11261:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11261:ℚ)^(-2:ℤ) : ℝ) = ((11261:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1362 : ((((113059698563 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11273, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11261 < q → q < 11273 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11273).mp (by decide +kernel))) hgap
  have hprev := s2L_1361
  have hrat : ((113059698563 : ℚ) / 250000000000) ≤ ((452238786383 : ℚ) / 1000000000000) + (11273:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059698563 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452238786383 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11273:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11273:ℚ)^(-2:ℤ) : ℝ) = ((11273:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1363 : ((((7066231283 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11279, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11273 < q → q < 11279 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11279).mp (by decide +kernel))) hgap
  have hprev := s2L_1362
  have hrat : ((7066231283 : ℚ) / 15625000000) ≤ ((113059698563 : ℚ) / 250000000000) + (11279:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((7066231283 : ℚ) / 15625000000) : ℚ) : ℝ) ≤ ((((113059698563 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11279:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11279:ℚ)^(-2:ℤ) : ℝ) = ((11279:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1364 : ((((452238809961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11287, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11279 < q → q < 11287 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11287).mp (by decide +kernel))) hgap
  have hprev := s2L_1363
  have hrat : ((452238809961 : ℚ) / 1000000000000) ≤ ((7066231283 : ℚ) / 15625000000) + (11287:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238809961 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((7066231283 : ℚ) / 15625000000) : ℚ) : ℝ) + ((11287:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11287:ℚ)^(-2:ℤ) : ℝ) = ((11287:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1365 : ((((452238817793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11299, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11287 < q → q < 11299 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11299).mp (by decide +kernel))) hgap
  have hprev := s2L_1364
  have hrat : ((452238817793 : ℚ) / 1000000000000) ≤ ((452238809961 : ℚ) / 1000000000000) + (11299:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238817793 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238809961 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11299:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11299:ℚ)^(-2:ℤ) : ℝ) = ((11299:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1366 : ((((452238825609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11311, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11299 < q → q < 11311 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11311).mp (by decide +kernel))) hgap
  have hprev := s2L_1365
  have hrat : ((452238825609 : ℚ) / 1000000000000) ≤ ((452238817793 : ℚ) / 1000000000000) + (11311:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238825609 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238817793 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11311:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11311:ℚ)^(-2:ℤ) : ℝ) = ((11311:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1367 : ((((56529854177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11317, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11311 < q → q < 11317 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11317).mp (by decide +kernel))) hgap
  have hprev := s2L_1366
  have hrat : ((56529854177 : ℚ) / 125000000000) ≤ ((452238825609 : ℚ) / 1000000000000) + (11317:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529854177 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452238825609 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11317:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11317:ℚ)^(-2:ℤ) : ℝ) = ((11317:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1368 : ((((226119420609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11321, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11317 < q → q < 11321 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11321).mp (by decide +kernel))) hgap
  have hprev := s2L_1367
  have hrat : ((226119420609 : ℚ) / 500000000000) ≤ ((56529854177 : ℚ) / 125000000000) + (11321:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119420609 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529854177 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11321:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11321:ℚ)^(-2:ℤ) : ℝ) = ((11321:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1369 : ((((452238849009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11321 < q → q < 11329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11329).mp (by decide +kernel))) hgap
  have hprev := s2L_1368
  have hrat : ((452238849009 : ℚ) / 1000000000000) ≤ ((226119420609 : ℚ) / 500000000000) + (11329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238849009 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119420609 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11329:ℚ)^(-2:ℤ) : ℝ) = ((11329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1370 : ((((45223885677 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11351, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11329 < q → q < 11351 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11351).mp (by decide +kernel))) hgap
  have hprev := s2L_1369
  have hrat : ((45223885677 : ℚ) / 100000000000) ≤ ((452238849009 : ℚ) / 1000000000000) + (11351:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223885677 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452238849009 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11351:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11351:ℚ)^(-2:ℤ) : ℝ) = ((11351:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1371 : ((((28264929033 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11353, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11351 < q → q < 11353 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11353).mp (by decide +kernel))) hgap
  have hprev := s2L_1370
  have hrat : ((28264929033 : ℚ) / 62500000000) ≤ ((45223885677 : ℚ) / 100000000000) + (11353:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264929033 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((45223885677 : ℚ) / 100000000000) : ℚ) : ℝ) + ((11353:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11353:ℚ)^(-2:ℤ) : ℝ) = ((11353:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1372 : ((((56529859033 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11369, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11353 < q → q < 11369 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11369).mp (by decide +kernel))) hgap
  have hprev := s2L_1371
  have hrat : ((56529859033 : ℚ) / 125000000000) ≤ ((28264929033 : ℚ) / 62500000000) + (11369:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529859033 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((28264929033 : ℚ) / 62500000000) : ℚ) : ℝ) + ((11369:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11369:ℚ)^(-2:ℤ) : ℝ) = ((11369:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1373 : ((((452238879981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11383, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11369 < q → q < 11383 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11383).mp (by decide +kernel))) hgap
  have hprev := s2L_1372
  have hrat : ((452238879981 : ℚ) / 1000000000000) ≤ ((56529859033 : ℚ) / 125000000000) + (11383:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238879981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529859033 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11383:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11383:ℚ)^(-2:ℤ) : ℝ) = ((11383:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1374 : ((((90447777537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11393, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11383 < q → q < 11393 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11393).mp (by decide +kernel))) hgap
  have hprev := s2L_1373
  have hrat : ((90447777537 : ℚ) / 200000000000) ≤ ((452238879981 : ℚ) / 1000000000000) + (11393:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447777537 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452238879981 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11393:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11393:ℚ)^(-2:ℤ) : ℝ) = ((11393:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1375 : ((((452238895381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11393 < q → q < 11399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11399).mp (by decide +kernel))) hgap
  have hprev := s2L_1374
  have hrat : ((452238895381 : ℚ) / 1000000000000) ≤ ((90447777537 : ℚ) / 200000000000) + (11399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238895381 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447777537 : ℚ) / 200000000000) : ℚ) : ℝ) + ((11399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11399:ℚ)^(-2:ℤ) : ℝ) = ((11399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1376 : ((((22611945153 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11399 < q → q < 11411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11411).mp (by decide +kernel))) hgap
  have hprev := s2L_1375
  have hrat : ((22611945153 : ℚ) / 50000000000) ≤ ((452238895381 : ℚ) / 1000000000000) + (11411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611945153 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((452238895381 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11411:ℚ)^(-2:ℤ) : ℝ) = ((11411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1377 : ((((452238910723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11423, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11411 < q → q < 11423 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11423).mp (by decide +kernel))) hgap
  have hprev := s2L_1376
  have hrat : ((452238910723 : ℚ) / 1000000000000) ≤ ((22611945153 : ℚ) / 50000000000) + (11423:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238910723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((22611945153 : ℚ) / 50000000000) : ℚ) : ℝ) + ((11423:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11423:ℚ)^(-2:ℤ) : ℝ) = ((11423:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1378 : ((((452238918367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11423 < q → q < 11437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11437).mp (by decide +kernel))) hgap
  have hprev := s2L_1377
  have hrat : ((452238918367 : ℚ) / 1000000000000) ≤ ((452238910723 : ℚ) / 1000000000000) + (11437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238918367 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238910723 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11437:ℚ)^(-2:ℤ) : ℝ) = ((11437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1379 : ((((452238926003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11443, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11437 < q → q < 11443 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11443).mp (by decide +kernel))) hgap
  have hprev := s2L_1378
  have hrat : ((452238926003 : ℚ) / 1000000000000) ≤ ((452238918367 : ℚ) / 1000000000000) + (11443:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238926003 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238918367 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11443:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11443:ℚ)^(-2:ℤ) : ℝ) = ((11443:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1380 : ((((226119466817 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11447, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11443 < q → q < 11447 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11447).mp (by decide +kernel))) hgap
  have hprev := s2L_1379
  have hrat : ((226119466817 : ℚ) / 500000000000) ≤ ((452238926003 : ℚ) / 1000000000000) + (11447:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119466817 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238926003 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11447:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11447:ℚ)^(-2:ℤ) : ℝ) = ((11447:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1381 : ((((452238941239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11467, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11447 < q → q < 11467 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11467).mp (by decide +kernel))) hgap
  have hprev := s2L_1380
  have hrat : ((452238941239 : ℚ) / 1000000000000) ≤ ((226119466817 : ℚ) / 500000000000) + (11467:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238941239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119466817 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11467:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11467:ℚ)^(-2:ℤ) : ℝ) = ((11467:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1382 : ((((226119474419 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11471, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11467 < q → q < 11471 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11471).mp (by decide +kernel))) hgap
  have hprev := s2L_1381
  have hrat : ((226119474419 : ℚ) / 500000000000) ≤ ((452238941239 : ℚ) / 1000000000000) + (11471:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119474419 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238941239 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11471:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11471:ℚ)^(-2:ℤ) : ℝ) = ((11471:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1383 : ((((452238956421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11483, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11471 < q → q < 11483 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11483).mp (by decide +kernel))) hgap
  have hprev := s2L_1382
  have hrat : ((452238956421 : ℚ) / 1000000000000) ≤ ((226119474419 : ℚ) / 500000000000) + (11483:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238956421 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119474419 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11483:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11483:ℚ)^(-2:ℤ) : ℝ) = ((11483:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1384 : ((((113059740999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11489, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11483 < q → q < 11489 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11489).mp (by decide +kernel))) hgap
  have hprev := s2L_1383
  have hrat : ((113059740999 : ℚ) / 250000000000) ≤ ((452238956421 : ℚ) / 1000000000000) + (11489:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059740999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452238956421 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11489:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11489:ℚ)^(-2:ℤ) : ℝ) = ((11489:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1385 : ((((452238971569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11489 < q → q < 11491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11491).mp (by decide +kernel))) hgap
  have hprev := s2L_1384
  have hrat : ((452238971569 : ℚ) / 1000000000000) ≤ ((113059740999 : ℚ) / 250000000000) + (11491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238971569 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059740999 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11491:ℚ)^(-2:ℤ) : ℝ) = ((11491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1386 : ((((226119489567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11491 < q → q < 11497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11497).mp (by decide +kernel))) hgap
  have hprev := s2L_1385
  have hrat : ((226119489567 : ℚ) / 500000000000) ≤ ((452238971569 : ℚ) / 1000000000000) + (11497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119489567 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452238971569 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11497:ℚ)^(-2:ℤ) : ℝ) = ((11497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1387 : ((((452238986691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11497 < q → q < 11503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11503).mp (by decide +kernel))) hgap
  have hprev := s2L_1386
  have hrat : ((452238986691 : ℚ) / 1000000000000) ≤ ((226119489567 : ℚ) / 500000000000) + (11503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238986691 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119489567 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11503:ℚ)^(-2:ℤ) : ℝ) = ((11503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1388 : ((((452238994227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11519, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11503 < q → q < 11519 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11519).mp (by decide +kernel))) hgap
  have hprev := s2L_1387
  have hrat : ((452238994227 : ℚ) / 1000000000000) ≤ ((452238986691 : ℚ) / 1000000000000) + (11519:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452238994227 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238986691 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11519:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11519:ℚ)^(-2:ℤ) : ℝ) = ((11519:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1389 : ((((452239001753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11519 < q → q < 11527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11527).mp (by decide +kernel))) hgap
  have hprev := s2L_1388
  have hrat : ((452239001753 : ℚ) / 1000000000000) ≤ ((452238994227 : ℚ) / 1000000000000) + (11527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239001753 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452238994227 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11527:ℚ)^(-2:ℤ) : ℝ) = ((11527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1390 : ((((1808956037 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11549, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11527 < q → q < 11549 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11549).mp (by decide +kernel))) hgap
  have hprev := s2L_1389
  have hrat : ((1808956037 : ℚ) / 4000000000) ≤ ((452239001753 : ℚ) / 1000000000000) + (11549:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808956037 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((452239001753 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11549:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11549:ℚ)^(-2:ℤ) : ℝ) = ((11549:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1391 : ((((56529877093 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11551, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11549 < q → q < 11551 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11551).mp (by decide +kernel))) hgap
  have hprev := s2L_1390
  have hrat : ((56529877093 : ℚ) / 125000000000) ≤ ((1808956037 : ℚ) / 4000000000) + (11551:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529877093 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((1808956037 : ℚ) / 4000000000) : ℚ) : ℝ) + ((11551:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11551:ℚ)^(-2:ℤ) : ℝ) = ((11551:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1392 : ((((226119512101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11579, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11551 < q → q < 11579 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11579).mp (by decide +kernel))) hgap
  have hprev := s2L_1391
  have hrat : ((226119512101 : ℚ) / 500000000000) ≤ ((56529877093 : ℚ) / 125000000000) + (11579:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119512101 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529877093 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11579:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11579:ℚ)^(-2:ℤ) : ℝ) = ((11579:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1393 : ((((9044780633 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11587, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11579 < q → q < 11587 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11587).mp (by decide +kernel))) hgap
  have hprev := s2L_1392
  have hrat : ((9044780633 : ℚ) / 20000000000) ≤ ((226119512101 : ℚ) / 500000000000) + (11587:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044780633 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((226119512101 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11587:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11587:ℚ)^(-2:ℤ) : ℝ) = ((11587:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1394 : ((((45223903909 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11593, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11587 < q → q < 11593 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11593).mp (by decide +kernel))) hgap
  have hprev := s2L_1393
  have hrat : ((45223903909 : ℚ) / 100000000000) ≤ ((9044780633 : ℚ) / 20000000000) + (11593:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223903909 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((9044780633 : ℚ) / 20000000000) : ℚ) : ℝ) + ((11593:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11593:ℚ)^(-2:ℤ) : ℝ) = ((11593:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1395 : ((((18089561861 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11597, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11593 < q → q < 11597 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11597).mp (by decide +kernel))) hgap
  have hprev := s2L_1394
  have hrat : ((18089561861 : ℚ) / 40000000000) ≤ ((45223903909 : ℚ) / 100000000000) + (11597:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089561861 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((45223903909 : ℚ) / 100000000000) : ℚ) : ℝ) + ((11597:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11597:ℚ)^(-2:ℤ) : ℝ) = ((11597:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1396 : ((((226119526967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11617, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11597 < q → q < 11617 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11617).mp (by decide +kernel))) hgap
  have hprev := s2L_1395
  have hrat : ((226119526967 : ℚ) / 500000000000) ≤ ((18089561861 : ℚ) / 40000000000) + (11617:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119526967 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((18089561861 : ℚ) / 40000000000) : ℚ) : ℝ) + ((11617:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11617:ℚ)^(-2:ℤ) : ℝ) = ((11617:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1397 : ((((226119530669 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11621, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11617 < q → q < 11621 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11621).mp (by decide +kernel))) hgap
  have hprev := s2L_1396
  have hrat : ((226119530669 : ℚ) / 500000000000) ≤ ((226119526967 : ℚ) / 500000000000) + (11621:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119530669 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119526967 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11621:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11621:ℚ)^(-2:ℤ) : ℝ) = ((11621:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1398 : ((((452239068727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11633, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11621 < q → q < 11633 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11633).mp (by decide +kernel))) hgap
  have hprev := s2L_1397
  have hrat : ((452239068727 : ℚ) / 1000000000000) ≤ ((226119530669 : ℚ) / 500000000000) + (11633:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239068727 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119530669 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11633:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11633:ℚ)^(-2:ℤ) : ℝ) = ((11633:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1399 : ((((226119538043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11657, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11633 < q → q < 11657 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11657).mp (by decide +kernel))) hgap
  have hprev := s2L_1398
  have hrat : ((226119538043 : ℚ) / 500000000000) ≤ ((452239068727 : ℚ) / 1000000000000) + (11657:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119538043 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239068727 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11657:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11657:ℚ)^(-2:ℤ) : ℝ) = ((11657:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1400 : ((((452239083419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11677, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11657 < q → q < 11677 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11677).mp (by decide +kernel))) hgap
  have hprev := s2L_1399
  have hrat : ((452239083419 : ℚ) / 1000000000000) ≤ ((226119538043 : ℚ) / 500000000000) + (11677:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239083419 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119538043 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11677:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11677:ℚ)^(-2:ℤ) : ℝ) = ((11677:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1401 : ((((452239090747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11681, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11677 < q → q < 11681 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11681).mp (by decide +kernel))) hgap
  have hprev := s2L_1400
  have hrat : ((452239090747 : ℚ) / 1000000000000) ≤ ((452239083419 : ℚ) / 1000000000000) + (11681:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239090747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239083419 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11681:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11681:ℚ)^(-2:ℤ) : ℝ) = ((11681:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1402 : ((((90447819613 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11681 < q → q < 11689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11689).mp (by decide +kernel))) hgap
  have hprev := s2L_1401
  have hrat : ((90447819613 : ℚ) / 200000000000) ≤ ((452239090747 : ℚ) / 1000000000000) + (11689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447819613 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452239090747 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11689:ℚ)^(-2:ℤ) : ℝ) = ((11689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1403 : ((((452239105371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11699, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11689 < q → q < 11699 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11699).mp (by decide +kernel))) hgap
  have hprev := s2L_1402
  have hrat : ((452239105371 : ℚ) / 1000000000000) ≤ ((90447819613 : ℚ) / 200000000000) + (11699:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239105371 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90447819613 : ℚ) / 200000000000) : ℚ) : ℝ) + ((11699:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11699:ℚ)^(-2:ℤ) : ℝ) = ((11699:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1404 : ((((226119556337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11701, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11699 < q → q < 11701 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11701).mp (by decide +kernel))) hgap
  have hprev := s2L_1403
  have hrat : ((226119556337 : ℚ) / 500000000000) ≤ ((452239105371 : ℚ) / 1000000000000) + (11701:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119556337 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239105371 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11701:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11701:ℚ)^(-2:ℤ) : ℝ) = ((11701:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1405 : ((((452239119957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11717, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11701 < q → q < 11717 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11717).mp (by decide +kernel))) hgap
  have hprev := s2L_1404
  have hrat : ((452239119957 : ℚ) / 1000000000000) ≤ ((226119556337 : ℚ) / 500000000000) + (11717:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239119957 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119556337 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11717:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11717:ℚ)^(-2:ℤ) : ℝ) = ((11717:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1406 : ((((226119563619 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11719, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11717 < q → q < 11719 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11719).mp (by decide +kernel))) hgap
  have hprev := s2L_1405
  have hrat : ((226119563619 : ℚ) / 500000000000) ≤ ((452239119957 : ℚ) / 1000000000000) + (11719:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119563619 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239119957 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11719:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11719:ℚ)^(-2:ℤ) : ℝ) = ((11719:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1407 : ((((56529891813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11731, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11719 < q → q < 11731 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11731).mp (by decide +kernel))) hgap
  have hprev := s2L_1406
  have hrat : ((56529891813 : ℚ) / 125000000000) ≤ ((226119563619 : ℚ) / 500000000000) + (11731:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529891813 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226119563619 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11731:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11731:ℚ)^(-2:ℤ) : ℝ) = ((11731:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1408 : ((((90447828351 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11731 < q → q < 11743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11743).mp (by decide +kernel))) hgap
  have hprev := s2L_1407
  have hrat : ((90447828351 : ℚ) / 200000000000) ≤ ((56529891813 : ℚ) / 125000000000) + (11743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447828351 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((56529891813 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11743:ℚ)^(-2:ℤ) : ℝ) = ((11743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1409 : ((((113059787241 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11777, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11743 < q → q < 11777 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11777).mp (by decide +kernel))) hgap
  have hprev := s2L_1408
  have hrat : ((113059787241 : ℚ) / 250000000000) ≤ ((90447828351 : ℚ) / 200000000000) + (11777:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059787241 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447828351 : ℚ) / 200000000000) : ℚ) : ℝ) + ((11777:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11777:ℚ)^(-2:ℤ) : ℝ) = ((11777:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1410 : ((((452239156171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11779, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11777 < q → q < 11779 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11779).mp (by decide +kernel))) hgap
  have hprev := s2L_1409
  have hrat : ((452239156171 : ℚ) / 1000000000000) ≤ ((113059787241 : ℚ) / 250000000000) + (11779:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239156171 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059787241 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11779:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11779:ℚ)^(-2:ℤ) : ℝ) = ((11779:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1411 : ((((452239163373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11783, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11779 < q → q < 11783 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11783).mp (by decide +kernel))) hgap
  have hprev := s2L_1410
  have hrat : ((452239163373 : ℚ) / 1000000000000) ≤ ((452239156171 : ℚ) / 1000000000000) + (11783:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239163373 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239156171 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11783:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11783:ℚ)^(-2:ℤ) : ℝ) = ((11783:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1412 : ((((56529896321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11789, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11783 < q → q < 11789 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11789).mp (by decide +kernel))) hgap
  have hprev := s2L_1411
  have hrat : ((56529896321 : ℚ) / 125000000000) ≤ ((452239163373 : ℚ) / 1000000000000) + (11789:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529896321 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239163373 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11789:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11789:ℚ)^(-2:ℤ) : ℝ) = ((11789:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1413 : ((((113059794437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11801, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11789 < q → q < 11801 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11801).mp (by decide +kernel))) hgap
  have hprev := s2L_1412
  have hrat : ((113059794437 : ℚ) / 250000000000) ≤ ((56529896321 : ℚ) / 125000000000) + (11801:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059794437 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((56529896321 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11801:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11801:ℚ)^(-2:ℤ) : ℝ) = ((11801:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1414 : ((((452239184921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11807, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11801 < q → q < 11807 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11807).mp (by decide +kernel))) hgap
  have hprev := s2L_1413
  have hrat : ((452239184921 : ℚ) / 1000000000000) ≤ ((113059794437 : ℚ) / 250000000000) + (11807:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239184921 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059794437 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11807:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11807:ℚ)^(-2:ℤ) : ℝ) = ((11807:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1415 : ((((452239192087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11813, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11807 < q → q < 11813 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11813).mp (by decide +kernel))) hgap
  have hprev := s2L_1414
  have hrat : ((452239192087 : ℚ) / 1000000000000) ≤ ((452239184921 : ℚ) / 1000000000000) + (11813:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239192087 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239184921 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11813:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11813:ℚ)^(-2:ℤ) : ℝ) = ((11813:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1416 : ((((452239199243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11813 < q → q < 11821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11821).mp (by decide +kernel))) hgap
  have hprev := s2L_1415
  have hrat : ((452239199243 : ℚ) / 1000000000000) ≤ ((452239192087 : ℚ) / 1000000000000) + (11821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239199243 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239192087 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11821:ℚ)^(-2:ℤ) : ℝ) = ((11821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1417 : ((((56529900799 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11827, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11821 < q → q < 11827 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11827).mp (by decide +kernel))) hgap
  have hprev := s2L_1416
  have hrat : ((56529900799 : ℚ) / 125000000000) ≤ ((452239199243 : ℚ) / 1000000000000) + (11827:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529900799 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239199243 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11827:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11827:ℚ)^(-2:ℤ) : ℝ) = ((11827:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1418 : ((((14132475423 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11831, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11827 < q → q < 11831 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11831).mp (by decide +kernel))) hgap
  have hprev := s2L_1417
  have hrat : ((14132475423 : ℚ) / 31250000000) ≤ ((56529900799 : ℚ) / 125000000000) + (11831:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132475423 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((56529900799 : ℚ) / 125000000000) : ℚ) : ℝ) + ((11831:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11831:ℚ)^(-2:ℤ) : ℝ) = ((11831:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1419 : ((((452239220677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11833, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11831 < q → q < 11833 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11833).mp (by decide +kernel))) hgap
  have hprev := s2L_1418
  have hrat : ((452239220677 : ℚ) / 1000000000000) ≤ ((14132475423 : ℚ) / 31250000000) + (11833:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239220677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132475423 : ℚ) / 31250000000) : ℚ) : ℝ) + ((11833:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11833:ℚ)^(-2:ℤ) : ℝ) = ((11833:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1420 : ((((452239227811 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11839, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11833 < q → q < 11839 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11839).mp (by decide +kernel))) hgap
  have hprev := s2L_1419
  have hrat : ((452239227811 : ℚ) / 1000000000000) ≤ ((452239220677 : ℚ) / 1000000000000) + (11839:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239227811 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239220677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11839:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11839:ℚ)^(-2:ℤ) : ℝ) = ((11839:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1421 : ((((113059808729 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11863, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11839 < q → q < 11863 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11863).mp (by decide +kernel))) hgap
  have hprev := s2L_1420
  have hrat : ((113059808729 : ℚ) / 250000000000) ≤ ((452239227811 : ℚ) / 1000000000000) + (11863:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059808729 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452239227811 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11863:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11863:ℚ)^(-2:ℤ) : ℝ) = ((11863:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1422 : ((((14132476313 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11867, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11863 < q → q < 11867 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11867).mp (by decide +kernel))) hgap
  have hprev := s2L_1421
  have hrat : ((14132476313 : ℚ) / 31250000000) ≤ ((113059808729 : ℚ) / 250000000000) + (11867:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132476313 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((113059808729 : ℚ) / 250000000000) : ℚ) : ℝ) + ((11867:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11867:ℚ)^(-2:ℤ) : ℝ) = ((11867:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1423 : ((((452239249093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11887, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11867 < q → q < 11887 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11887).mp (by decide +kernel))) hgap
  have hprev := s2L_1422
  have hrat : ((452239249093 : ℚ) / 1000000000000) ≤ ((14132476313 : ℚ) / 31250000000) + (11887:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239249093 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((14132476313 : ℚ) / 31250000000) : ℚ) : ℝ) + ((11887:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11887:ℚ)^(-2:ℤ) : ℝ) = ((11887:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1424 : ((((226119628079 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11897, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11887 < q → q < 11897 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11897).mp (by decide +kernel))) hgap
  have hprev := s2L_1423
  have hrat : ((226119628079 : ℚ) / 500000000000) ≤ ((452239249093 : ℚ) / 1000000000000) + (11897:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119628079 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239249093 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11897:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11897:ℚ)^(-2:ℤ) : ℝ) = ((11897:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1425 : ((((28264953951 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11903, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11897 < q → q < 11903 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11903).mp (by decide +kernel))) hgap
  have hprev := s2L_1424
  have hrat : ((28264953951 : ℚ) / 62500000000) ≤ ((226119628079 : ℚ) / 500000000000) + (11903:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264953951 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226119628079 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11903:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11903:ℚ)^(-2:ℤ) : ℝ) = ((11903:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1426 : ((((226119635133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11909, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11903 < q → q < 11909 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11909).mp (by decide +kernel))) hgap
  have hprev := s2L_1425
  have hrat : ((226119635133 : ℚ) / 500000000000) ≤ ((28264953951 : ℚ) / 62500000000) + (11909:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119635133 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264953951 : ℚ) / 62500000000) : ℚ) : ℝ) + ((11909:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11909:ℚ)^(-2:ℤ) : ℝ) = ((11909:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1427 : ((((4522392773 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11909 < q → q < 11923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11923).mp (by decide +kernel))) hgap
  have hprev := s2L_1426
  have hrat : ((4522392773 : ℚ) / 10000000000) ≤ ((226119635133 : ℚ) / 500000000000) + (11923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522392773 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((226119635133 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11923:ℚ)^(-2:ℤ) : ℝ) = ((11923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1428 : ((((452239284329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11927, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11923 < q → q < 11927 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11927).mp (by decide +kernel))) hgap
  have hprev := s2L_1427
  have hrat : ((452239284329 : ℚ) / 1000000000000) ≤ ((4522392773 : ℚ) / 10000000000) + (11927:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239284329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((4522392773 : ℚ) / 10000000000) : ℚ) : ℝ) + ((11927:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11927:ℚ)^(-2:ℤ) : ℝ) = ((11927:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1429 : ((((452239291351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11933, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11927 < q → q < 11933 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11933).mp (by decide +kernel))) hgap
  have hprev := s2L_1428
  have hrat : ((452239291351 : ℚ) / 1000000000000) ≤ ((452239284329 : ℚ) / 1000000000000) + (11933:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239291351 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239284329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11933:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11933:ℚ)^(-2:ℤ) : ℝ) = ((11933:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1430 : ((((226119649183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11939, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11933 < q → q < 11939 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11939).mp (by decide +kernel))) hgap
  have hprev := s2L_1429
  have hrat : ((226119649183 : ℚ) / 500000000000) ≤ ((452239291351 : ℚ) / 1000000000000) + (11939:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119649183 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239291351 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11939:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11939:ℚ)^(-2:ℤ) : ℝ) = ((11939:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1431 : ((((452239305379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11939 < q → q < 11941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11941).mp (by decide +kernel))) hgap
  have hprev := s2L_1430
  have hrat : ((452239305379 : ℚ) / 1000000000000) ≤ ((226119649183 : ℚ) / 500000000000) + (11941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239305379 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119649183 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11941:ℚ)^(-2:ℤ) : ℝ) = ((11941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1432 : ((((226119656189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11941 < q → q < 11953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11953).mp (by decide +kernel))) hgap
  have hprev := s2L_1431
  have hrat : ((226119656189 : ℚ) / 500000000000) ≤ ((452239305379 : ℚ) / 1000000000000) + (11953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119656189 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239305379 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((11953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11953:ℚ)^(-2:ℤ) : ℝ) = ((11953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1433 : ((((45223931937 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11953 < q → q < 11959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11959).mp (by decide +kernel))) hgap
  have hprev := s2L_1432
  have hrat : ((45223931937 : ℚ) / 100000000000) ≤ ((226119656189 : ℚ) / 500000000000) + (11959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223931937 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((226119656189 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11959:ℚ)^(-2:ℤ) : ℝ) = ((11959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1434 : ((((9044786527 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11969, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11959 < q → q < 11969 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11969).mp (by decide +kernel))) hgap
  have hprev := s2L_1433
  have hrat : ((9044786527 : ℚ) / 20000000000) ≤ ((45223931937 : ℚ) / 100000000000) + (11969:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044786527 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((45223931937 : ℚ) / 100000000000) : ℚ) : ℝ) + ((11969:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11969:ℚ)^(-2:ℤ) : ℝ) = ((11969:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1435 : ((((28264958333 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11971, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11969 < q → q < 11971 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11971).mp (by decide +kernel))) hgap
  have hprev := s2L_1434
  have hrat : ((28264958333 : ℚ) / 62500000000) ≤ ((9044786527 : ℚ) / 20000000000) + (11971:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264958333 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((9044786527 : ℚ) / 20000000000) : ℚ) : ℝ) + ((11971:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11971:ℚ)^(-2:ℤ) : ℝ) = ((11971:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1436 : ((((226119670147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11981, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11971 < q → q < 11981 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11981).mp (by decide +kernel))) hgap
  have hprev := s2L_1435
  have hrat : ((226119670147 : ℚ) / 500000000000) ≤ ((28264958333 : ℚ) / 62500000000) + (11981:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119670147 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264958333 : ℚ) / 62500000000) : ℚ) : ℝ) + ((11981:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11981:ℚ)^(-2:ℤ) : ℝ) = ((11981:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1437 : ((((452239347253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 11987, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11981 < q → q < 11987 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 11987).mp (by decide +kernel))) hgap
  have hprev := s2L_1436
  have hrat : ((452239347253 : ℚ) / 1000000000000) ≤ ((226119670147 : ℚ) / 500000000000) + (11987:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239347253 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119670147 : ℚ) / 500000000000) : ℚ) : ℝ) + ((11987:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((11987:ℚ)^(-2:ℤ) : ℝ) = ((11987:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1438 : ((((452239354189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 11987 < q → q < 12007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12007).mp (by decide +kernel))) hgap
  have hprev := s2L_1437
  have hrat : ((452239354189 : ℚ) / 1000000000000) ≤ ((452239347253 : ℚ) / 1000000000000) + (12007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239354189 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239347253 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12007:ℚ)^(-2:ℤ) : ℝ) = ((12007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1439 : ((((2826496007 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12011, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12007 < q → q < 12011 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12011).mp (by decide +kernel))) hgap
  have hprev := s2L_1438
  have hrat : ((2826496007 : ℚ) / 6250000000) ≤ ((452239354189 : ℚ) / 1000000000000) + (12011:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((2826496007 : ℚ) / 6250000000) : ℚ) : ℝ) ≤ ((((452239354189 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12011:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12011:ℚ)^(-2:ℤ) : ℝ) = ((12011:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1440 : ((((452239368021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12011 < q → q < 12037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12037).mp (by decide +kernel))) hgap
  have hprev := s2L_1439
  have hrat : ((452239368021 : ℚ) / 1000000000000) ≤ ((2826496007 : ℚ) / 6250000000) + (12037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239368021 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((2826496007 : ℚ) / 6250000000) : ℚ) : ℝ) + ((12037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12037:ℚ)^(-2:ℤ) : ℝ) = ((12037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1441 : ((((226119687459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12041, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12037 < q → q < 12041 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12041).mp (by decide +kernel))) hgap
  have hprev := s2L_1440
  have hrat : ((226119687459 : ℚ) / 500000000000) ≤ ((452239368021 : ℚ) / 1000000000000) + (12041:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119687459 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239368021 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12041:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12041:ℚ)^(-2:ℤ) : ℝ) = ((12041:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1442 : ((((113059845453 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12041 < q → q < 12043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12043).mp (by decide +kernel))) hgap
  have hprev := s2L_1441
  have hrat : ((113059845453 : ℚ) / 250000000000) ≤ ((226119687459 : ℚ) / 500000000000) + (12043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059845453 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119687459 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12043:ℚ)^(-2:ℤ) : ℝ) = ((12043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1443 : ((((4522393887 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12043 < q → q < 12049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12049).mp (by decide +kernel))) hgap
  have hprev := s2L_1442
  have hrat : ((4522393887 : ℚ) / 10000000000) ≤ ((113059845453 : ℚ) / 250000000000) + (12049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((4522393887 : ℚ) / 10000000000) : ℚ) : ℝ) ≤ ((((113059845453 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12049:ℚ)^(-2:ℤ) : ℝ) = ((12049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1444 : ((((226119697781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12071, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12049 < q → q < 12071 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12071).mp (by decide +kernel))) hgap
  have hprev := s2L_1443
  have hrat : ((226119697781 : ℚ) / 500000000000) ≤ ((4522393887 : ℚ) / 10000000000) + (12071:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119697781 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((4522393887 : ℚ) / 10000000000) : ℚ) : ℝ) + ((12071:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12071:ℚ)^(-2:ℤ) : ℝ) = ((12071:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1445 : ((((226119701211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12073, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12071 < q → q < 12073 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12073).mp (by decide +kernel))) hgap
  have hprev := s2L_1444
  have hrat : ((226119701211 : ℚ) / 500000000000) ≤ ((226119697781 : ℚ) / 500000000000) + (12073:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119701211 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119697781 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12073:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12073:ℚ)^(-2:ℤ) : ℝ) = ((12073:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1446 : ((((90447881851 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12097, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12073 < q → q < 12097 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12097).mp (by decide +kernel))) hgap
  have hprev := s2L_1445
  have hrat : ((90447881851 : ℚ) / 200000000000) ≤ ((226119701211 : ℚ) / 500000000000) + (12097:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447881851 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119701211 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12097:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12097:ℚ)^(-2:ℤ) : ℝ) = ((12097:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1447 : ((((113059854021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12101, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12097 < q → q < 12101 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12101).mp (by decide +kernel))) hgap
  have hprev := s2L_1446
  have hrat : ((113059854021 : ℚ) / 250000000000) ≤ ((90447881851 : ℚ) / 200000000000) + (12101:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059854021 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447881851 : ℚ) / 200000000000) : ℚ) : ℝ) + ((12101:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12101:ℚ)^(-2:ℤ) : ℝ) = ((12101:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1448 : ((((226119711453 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12107, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12101 < q → q < 12107 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12107).mp (by decide +kernel))) hgap
  have hprev := s2L_1447
  have hrat : ((226119711453 : ℚ) / 500000000000) ≤ ((113059854021 : ℚ) / 250000000000) + (12107:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119711453 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059854021 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12107:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12107:ℚ)^(-2:ℤ) : ℝ) = ((12107:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1449 : ((((18089577189 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12107 < q → q < 12109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12109).mp (by decide +kernel))) hgap
  have hprev := s2L_1448
  have hrat : ((18089577189 : ℚ) / 40000000000) ≤ ((226119711453 : ℚ) / 500000000000) + (12109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089577189 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226119711453 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12109:ℚ)^(-2:ℤ) : ℝ) = ((12109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1450 : ((((22611971827 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12113, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12109 < q → q < 12113 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12113).mp (by decide +kernel))) hgap
  have hprev := s2L_1449
  have hrat : ((22611971827 : ℚ) / 50000000000) ≤ ((18089577189 : ℚ) / 40000000000) + (12113:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611971827 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18089577189 : ℚ) / 40000000000) : ℚ) : ℝ) + ((12113:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12113:ℚ)^(-2:ℤ) : ℝ) = ((12113:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1451 : ((((113059860837 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12119, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12113 < q → q < 12119 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12119).mp (by decide +kernel))) hgap
  have hprev := s2L_1450
  have hrat : ((113059860837 : ℚ) / 250000000000) ≤ ((22611971827 : ℚ) / 50000000000) + (12119:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059860837 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((22611971827 : ℚ) / 50000000000) : ℚ) : ℝ) + ((12119:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12119:ℚ)^(-2:ℤ) : ℝ) = ((12119:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1452 : ((((452239450129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12143, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12119 < q → q < 12143 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12143).mp (by decide +kernel))) hgap
  have hprev := s2L_1451
  have hrat : ((452239450129 : ℚ) / 1000000000000) ≤ ((113059860837 : ℚ) / 250000000000) + (12143:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239450129 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059860837 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12143:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12143:ℚ)^(-2:ℤ) : ℝ) = ((12143:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1453 : ((((56529932113 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12149, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12143 < q → q < 12149 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12149).mp (by decide +kernel))) hgap
  have hprev := s2L_1452
  have hrat : ((56529932113 : ℚ) / 125000000000) ≤ ((452239450129 : ℚ) / 1000000000000) + (12149:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529932113 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239450129 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12149:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12149:ℚ)^(-2:ℤ) : ℝ) = ((12149:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1454 : ((((45223946367 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12157, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12149 < q → q < 12157 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12157).mp (by decide +kernel))) hgap
  have hprev := s2L_1453
  have hrat : ((45223946367 : ℚ) / 100000000000) ≤ ((56529932113 : ℚ) / 125000000000) + (12157:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223946367 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((56529932113 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12157:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12157:ℚ)^(-2:ℤ) : ℝ) = ((12157:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1455 : ((((452239470431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12161, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12157 < q → q < 12161 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12161).mp (by decide +kernel))) hgap
  have hprev := s2L_1454
  have hrat : ((452239470431 : ℚ) / 1000000000000) ≤ ((45223946367 : ℚ) / 100000000000) + (12161:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239470431 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223946367 : ℚ) / 100000000000) : ℚ) : ℝ) + ((12161:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12161:ℚ)^(-2:ℤ) : ℝ) = ((12161:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1456 : ((((45223947719 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12161 < q → q < 12163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12163).mp (by decide +kernel))) hgap
  have hprev := s2L_1455
  have hrat : ((45223947719 : ℚ) / 100000000000) ≤ ((452239470431 : ℚ) / 1000000000000) + (12163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223947719 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((452239470431 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12163:ℚ)^(-2:ℤ) : ℝ) = ((12163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1457 : ((((452239483911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12197, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12163 < q → q < 12197 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12197).mp (by decide +kernel))) hgap
  have hprev := s2L_1456
  have hrat : ((452239483911 : ℚ) / 1000000000000) ≤ ((45223947719 : ℚ) / 100000000000) + (12197:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239483911 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223947719 : ℚ) / 100000000000) : ℚ) : ℝ) + ((12197:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12197:ℚ)^(-2:ℤ) : ℝ) = ((12197:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1458 : ((((226119745313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12203, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12197 < q → q < 12203 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12203).mp (by decide +kernel))) hgap
  have hprev := s2L_1457
  have hrat : ((226119745313 : ℚ) / 500000000000) ≤ ((452239483911 : ℚ) / 1000000000000) + (12203:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119745313 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239483911 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12203:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12203:ℚ)^(-2:ℤ) : ℝ) = ((12203:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1459 : ((((113059874333 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12211, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12203 < q → q < 12211 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12211).mp (by decide +kernel))) hgap
  have hprev := s2L_1458
  have hrat : ((113059874333 : ℚ) / 250000000000) ≤ ((226119745313 : ℚ) / 500000000000) + (12211:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059874333 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119745313 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12211:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12211:ℚ)^(-2:ℤ) : ℝ) = ((12211:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1460 : ((((22611975201 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12227, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12211 < q → q < 12227 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12227).mp (by decide +kernel))) hgap
  have hprev := s2L_1459
  have hrat : ((22611975201 : ℚ) / 50000000000) ≤ ((113059874333 : ℚ) / 250000000000) + (12227:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611975201 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((113059874333 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12227:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12227:ℚ)^(-2:ℤ) : ℝ) = ((12227:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1461 : ((((90447902139 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12239, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12227 < q → q < 12239 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12239).mp (by decide +kernel))) hgap
  have hprev := s2L_1460
  have hrat : ((90447902139 : ℚ) / 200000000000) ≤ ((22611975201 : ℚ) / 50000000000) + (12239:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447902139 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((22611975201 : ℚ) / 50000000000) : ℚ) : ℝ) + ((12239:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12239:ℚ)^(-2:ℤ) : ℝ) = ((12239:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1462 : ((((56529939671 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12239 < q → q < 12241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12241).mp (by decide +kernel))) hgap
  have hprev := s2L_1461
  have hrat : ((56529939671 : ℚ) / 125000000000) ≤ ((90447902139 : ℚ) / 200000000000) + (12241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529939671 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((90447902139 : ℚ) / 200000000000) : ℚ) : ℝ) + ((12241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12241:ℚ)^(-2:ℤ) : ℝ) = ((12241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1463 : ((((45223952403 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12251, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12241 < q → q < 12251 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12251).mp (by decide +kernel))) hgap
  have hprev := s2L_1462
  have hrat : ((45223952403 : ℚ) / 100000000000) ≤ ((56529939671 : ℚ) / 125000000000) + (12251:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223952403 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((56529939671 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12251:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12251:ℚ)^(-2:ℤ) : ℝ) = ((12251:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1464 : ((((45223953069 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12253, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12251 < q → q < 12253 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12253).mp (by decide +kernel))) hgap
  have hprev := s2L_1463
  have hrat : ((45223953069 : ℚ) / 100000000000) ≤ ((45223952403 : ℚ) / 100000000000) + (12253:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45223953069 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((45223952403 : ℚ) / 100000000000) : ℚ) : ℝ) + ((12253:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12253:ℚ)^(-2:ℤ) : ℝ) = ((12253:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1465 : ((((452239537339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12263, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12253 < q → q < 12263 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12263).mp (by decide +kernel))) hgap
  have hprev := s2L_1464
  have hrat : ((452239537339 : ℚ) / 1000000000000) ≤ ((45223953069 : ℚ) / 100000000000) + (12263:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239537339 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((45223953069 : ℚ) / 100000000000) : ℚ) : ℝ) + ((12263:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12263:ℚ)^(-2:ℤ) : ℝ) = ((12263:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1466 : ((((226119771991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12269, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12263 < q → q < 12269 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12269).mp (by decide +kernel))) hgap
  have hprev := s2L_1465
  have hrat : ((226119771991 : ℚ) / 500000000000) ≤ ((452239537339 : ℚ) / 1000000000000) + (12269:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119771991 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239537339 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12269:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12269:ℚ)^(-2:ℤ) : ℝ) = ((12269:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1467 : ((((56529943827 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12277, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12269 < q → q < 12277 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12277).mp (by decide +kernel))) hgap
  have hprev := s2L_1466
  have hrat : ((56529943827 : ℚ) / 125000000000) ≤ ((226119771991 : ℚ) / 500000000000) + (12277:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529943827 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((226119771991 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12277:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12277:ℚ)^(-2:ℤ) : ℝ) = ((12277:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1468 : ((((226119778623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12281, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12277 < q → q < 12281 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12281).mp (by decide +kernel))) hgap
  have hprev := s2L_1467
  have hrat : ((226119778623 : ℚ) / 500000000000) ≤ ((56529943827 : ℚ) / 125000000000) + (12281:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119778623 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529943827 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12281:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12281:ℚ)^(-2:ℤ) : ℝ) = ((12281:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1469 : ((((452239563867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12289, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12281 < q → q < 12289 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12289).mp (by decide +kernel))) hgap
  have hprev := s2L_1468
  have hrat : ((452239563867 : ℚ) / 1000000000000) ≤ ((226119778623 : ℚ) / 500000000000) + (12289:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239563867 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119778623 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12289:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12289:ℚ)^(-2:ℤ) : ℝ) = ((12289:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1470 : ((((18089582819 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12301, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12289 < q → q < 12301 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12301).mp (by decide +kernel))) hgap
  have hprev := s2L_1469
  have hrat : ((18089582819 : ℚ) / 40000000000) ≤ ((452239563867 : ℚ) / 1000000000000) + (12301:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089582819 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452239563867 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12301:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12301:ℚ)^(-2:ℤ) : ℝ) = ((12301:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1471 : ((((22611978853 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12323, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12301 < q → q < 12323 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12323).mp (by decide +kernel))) hgap
  have hprev := s2L_1470
  have hrat : ((22611978853 : ℚ) / 50000000000) ≤ ((18089582819 : ℚ) / 40000000000) + (12323:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611978853 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((18089582819 : ℚ) / 40000000000) : ℚ) : ℝ) + ((12323:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12323:ℚ)^(-2:ℤ) : ℝ) = ((12323:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1472 : ((((226119791819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12329, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12323 < q → q < 12329 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12329).mp (by decide +kernel))) hgap
  have hprev := s2L_1471
  have hrat : ((226119791819 : ℚ) / 500000000000) ≤ ((22611978853 : ℚ) / 50000000000) + (12329:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119791819 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((22611978853 : ℚ) / 50000000000) : ℚ) : ℝ) + ((12329:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12329:ℚ)^(-2:ℤ) : ℝ) = ((12329:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1473 : ((((452239590201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12343, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12329 < q → q < 12343 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12343).mp (by decide +kernel))) hgap
  have hprev := s2L_1472
  have hrat : ((452239590201 : ℚ) / 1000000000000) ≤ ((226119791819 : ℚ) / 500000000000) + (12343:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239590201 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119791819 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12343:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12343:ℚ)^(-2:ℤ) : ℝ) = ((12343:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1474 : ((((11305989919 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12347, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12343 < q → q < 12347 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12347).mp (by decide +kernel))) hgap
  have hprev := s2L_1473
  have hrat : ((11305989919 : ℚ) / 25000000000) ≤ ((452239590201 : ℚ) / 1000000000000) + (12347:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11305989919 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((452239590201 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12347:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12347:ℚ)^(-2:ℤ) : ℝ) = ((12347:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1475 : ((((113059900823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12373, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12347 < q → q < 12373 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12373).mp (by decide +kernel))) hgap
  have hprev := s2L_1474
  have hrat : ((113059900823 : ℚ) / 250000000000) ≤ ((11305989919 : ℚ) / 25000000000) + (12373:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059900823 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((11305989919 : ℚ) / 25000000000) : ℚ) : ℝ) + ((12373:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12373:ℚ)^(-2:ℤ) : ℝ) = ((12373:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1476 : ((((452239609819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12377, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12373 < q → q < 12377 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12377).mp (by decide +kernel))) hgap
  have hprev := s2L_1475
  have hrat : ((452239609819 : ℚ) / 1000000000000) ≤ ((113059900823 : ℚ) / 250000000000) + (12377:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239609819 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059900823 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12377:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12377:ℚ)^(-2:ℤ) : ℝ) = ((12377:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1477 : ((((56529952043 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12379, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12377 < q → q < 12379 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12379).mp (by decide +kernel))) hgap
  have hprev := s2L_1476
  have hrat : ((56529952043 : ℚ) / 125000000000) ≤ ((452239609819 : ℚ) / 1000000000000) + (12379:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529952043 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239609819 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12379:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12379:ℚ)^(-2:ℤ) : ℝ) = ((12379:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1478 : ((((452239622857 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12391, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12379 < q → q < 12391 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12391).mp (by decide +kernel))) hgap
  have hprev := s2L_1477
  have hrat : ((452239622857 : ℚ) / 1000000000000) ≤ ((56529952043 : ℚ) / 125000000000) + (12391:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239622857 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529952043 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12391:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12391:ℚ)^(-2:ℤ) : ℝ) = ((12391:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1479 : ((((452239629359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12401, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12391 < q → q < 12401 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12401).mp (by decide +kernel))) hgap
  have hprev := s2L_1478
  have hrat : ((452239629359 : ℚ) / 1000000000000) ≤ ((452239622857 : ℚ) / 1000000000000) + (12401:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239629359 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239622857 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12401:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12401:ℚ)^(-2:ℤ) : ℝ) = ((12401:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1480 : ((((452239635853 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12409, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12401 < q → q < 12409 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12409).mp (by decide +kernel))) hgap
  have hprev := s2L_1479
  have hrat : ((452239635853 : ℚ) / 1000000000000) ≤ ((452239629359 : ℚ) / 1000000000000) + (12409:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239635853 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239629359 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12409:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12409:ℚ)^(-2:ℤ) : ℝ) = ((12409:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1481 : ((((452239642343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12413, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12409 < q → q < 12413 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12413).mp (by decide +kernel))) hgap
  have hprev := s2L_1480
  have hrat : ((452239642343 : ℚ) / 1000000000000) ≤ ((452239635853 : ℚ) / 1000000000000) + (12413:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239642343 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239635853 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12413:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12413:ℚ)^(-2:ℤ) : ℝ) = ((12413:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1482 : ((((56529956103 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12413 < q → q < 12421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12421).mp (by decide +kernel))) hgap
  have hprev := s2L_1481
  have hrat : ((56529956103 : ℚ) / 125000000000) ≤ ((452239642343 : ℚ) / 1000000000000) + (12421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529956103 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239642343 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12421:ℚ)^(-2:ℤ) : ℝ) = ((12421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1483 : ((((452239655293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12433, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12421 < q → q < 12433 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12433).mp (by decide +kernel))) hgap
  have hprev := s2L_1482
  have hrat : ((452239655293 : ℚ) / 1000000000000) ≤ ((56529956103 : ℚ) / 125000000000) + (12433:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239655293 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529956103 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12433:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12433:ℚ)^(-2:ℤ) : ℝ) = ((12433:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1484 : ((((226119830879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12437, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12433 < q → q < 12437 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12437).mp (by decide +kernel))) hgap
  have hprev := s2L_1483
  have hrat : ((226119830879 : ℚ) / 500000000000) ≤ ((452239655293 : ℚ) / 1000000000000) + (12437:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119830879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239655293 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12437:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12437:ℚ)^(-2:ℤ) : ℝ) = ((12437:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1485 : ((((28264979263 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12437 < q → q < 12451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12451).mp (by decide +kernel))) hgap
  have hprev := s2L_1484
  have hrat : ((28264979263 : ℚ) / 62500000000) ≤ ((226119830879 : ℚ) / 500000000000) + (12451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264979263 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((226119830879 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12451:ℚ)^(-2:ℤ) : ℝ) = ((12451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1486 : ((((113059918663 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12451 < q → q < 12457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12457).mp (by decide +kernel))) hgap
  have hprev := s2L_1485
  have hrat : ((113059918663 : ℚ) / 250000000000) ≤ ((28264979263 : ℚ) / 62500000000) + (12457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059918663 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((28264979263 : ℚ) / 62500000000) : ℚ) : ℝ) + ((12457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12457:ℚ)^(-2:ℤ) : ℝ) = ((12457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1487 : ((((452239681079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12473, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12457 < q → q < 12473 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12473).mp (by decide +kernel))) hgap
  have hprev := s2L_1486
  have hrat : ((452239681079 : ℚ) / 1000000000000) ≤ ((113059918663 : ℚ) / 250000000000) + (12473:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239681079 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059918663 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12473:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12473:ℚ)^(-2:ℤ) : ℝ) = ((12473:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1488 : ((((1447167 : ℚ) / 3200000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12479, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12473 < q → q < 12479 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12479).mp (by decide +kernel))) hgap
  have hprev := s2L_1487
  have hrat : ((1447167 : ℚ) / 3200000) ≤ ((452239681079 : ℚ) / 1000000000000) + (12479:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1447167 : ℚ) / 3200000) : ℚ) : ℝ) ≤ ((((452239681079 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12479:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12479:ℚ)^(-2:ℤ) : ℝ) = ((12479:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1489 : ((((452239693913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12479 < q → q < 12487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12487).mp (by decide +kernel))) hgap
  have hprev := s2L_1488
  have hrat : ((452239693913 : ℚ) / 1000000000000) ≤ ((1447167 : ℚ) / 3200000) + (12487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239693913 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1447167 : ℚ) / 3200000) : ℚ) : ℝ) + ((12487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12487:ℚ)^(-2:ℤ) : ℝ) = ((12487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1490 : ((((226119850161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12491, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12487 < q → q < 12491 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12491).mp (by decide +kernel))) hgap
  have hprev := s2L_1489
  have hrat : ((226119850161 : ℚ) / 500000000000) ≤ ((452239693913 : ℚ) / 1000000000000) + (12491:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119850161 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239693913 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12491:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12491:ℚ)^(-2:ℤ) : ℝ) = ((12491:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1491 : ((((18089588269 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12497, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12491 < q → q < 12497 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12497).mp (by decide +kernel))) hgap
  have hprev := s2L_1490
  have hrat : ((18089588269 : ℚ) / 40000000000) ≤ ((226119850161 : ℚ) / 500000000000) + (12497:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089588269 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226119850161 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12497:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12497:ℚ)^(-2:ℤ) : ℝ) = ((12497:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1492 : ((((452239713121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12503, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12497 < q → q < 12503 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12503).mp (by decide +kernel))) hgap
  have hprev := s2L_1491
  have hrat : ((452239713121 : ℚ) / 1000000000000) ≤ ((18089588269 : ℚ) / 40000000000) + (12503:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239713121 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089588269 : ℚ) / 40000000000) : ℚ) : ℝ) + ((12503:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12503:ℚ)^(-2:ℤ) : ℝ) = ((12503:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1493 : ((((452239719509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12511, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12503 < q → q < 12511 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12511).mp (by decide +kernel))) hgap
  have hprev := s2L_1492
  have hrat : ((452239719509 : ℚ) / 1000000000000) ≤ ((452239713121 : ℚ) / 1000000000000) + (12511:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239719509 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239713121 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12511:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12511:ℚ)^(-2:ℤ) : ℝ) = ((12511:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1494 : ((((452239725891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12517, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12511 < q → q < 12517 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12517).mp (by decide +kernel))) hgap
  have hprev := s2L_1493
  have hrat : ((452239725891 : ℚ) / 1000000000000) ≤ ((452239719509 : ℚ) / 1000000000000) + (12517:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239725891 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239719509 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12517:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12517:ℚ)^(-2:ℤ) : ℝ) = ((12517:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1495 : ((((452239732263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12527, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12517 < q → q < 12527 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12527).mp (by decide +kernel))) hgap
  have hprev := s2L_1494
  have hrat : ((452239732263 : ℚ) / 1000000000000) ≤ ((452239725891 : ℚ) / 1000000000000) + (12527:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239732263 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239725891 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12527:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12527:ℚ)^(-2:ℤ) : ℝ) = ((12527:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1496 : ((((452239738623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12539, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12527 < q → q < 12539 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12539).mp (by decide +kernel))) hgap
  have hprev := s2L_1495
  have hrat : ((452239738623 : ℚ) / 1000000000000) ≤ ((452239732263 : ℚ) / 1000000000000) + (12539:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239738623 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239732263 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12539:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12539:ℚ)^(-2:ℤ) : ℝ) = ((12539:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1497 : ((((452239744981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12541, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12539 < q → q < 12541 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12541).mp (by decide +kernel))) hgap
  have hprev := s2L_1496
  have hrat : ((452239744981 : ℚ) / 1000000000000) ≤ ((452239738623 : ℚ) / 1000000000000) + (12541:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239744981 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239738623 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12541:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12541:ℚ)^(-2:ℤ) : ℝ) = ((12541:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1498 : ((((452239751333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12547, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12541 < q → q < 12547 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12547).mp (by decide +kernel))) hgap
  have hprev := s2L_1497
  have hrat : ((452239751333 : ℚ) / 1000000000000) ≤ ((452239744981 : ℚ) / 1000000000000) + (12547:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239751333 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239744981 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12547:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12547:ℚ)^(-2:ℤ) : ℝ) = ((12547:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1499 : ((((452239757679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12553, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12547 < q → q < 12553 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12553).mp (by decide +kernel))) hgap
  have hprev := s2L_1498
  have hrat : ((452239757679 : ℚ) / 1000000000000) ≤ ((452239751333 : ℚ) / 1000000000000) + (12553:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239757679 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239751333 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12553:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12553:ℚ)^(-2:ℤ) : ℝ) = ((12553:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1500 : ((((56529970501 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12569, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12553 < q → q < 12569 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12569).mp (by decide +kernel))) hgap
  have hprev := s2L_1499
  have hrat : ((56529970501 : ℚ) / 125000000000) ≤ ((452239757679 : ℚ) / 1000000000000) + (12569:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529970501 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452239757679 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12569:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12569:ℚ)^(-2:ℤ) : ℝ) = ((12569:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1501 : ((((452239770329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12577, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12569 < q → q < 12577 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12577).mp (by decide +kernel))) hgap
  have hprev := s2L_1500
  have hrat : ((452239770329 : ℚ) / 1000000000000) ≤ ((56529970501 : ℚ) / 125000000000) + (12577:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239770329 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56529970501 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12577:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12577:ℚ)^(-2:ℤ) : ℝ) = ((12577:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1502 : ((((113059944161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12583, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12577 < q → q < 12583 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12583).mp (by decide +kernel))) hgap
  have hprev := s2L_1501
  have hrat : ((113059944161 : ℚ) / 250000000000) ≤ ((452239770329 : ℚ) / 1000000000000) + (12583:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059944161 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452239770329 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12583:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12583:ℚ)^(-2:ℤ) : ℝ) = ((12583:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1503 : ((((452239782953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12589, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12583 < q → q < 12589 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12589).mp (by decide +kernel))) hgap
  have hprev := s2L_1502
  have hrat : ((452239782953 : ℚ) / 1000000000000) ≤ ((113059944161 : ℚ) / 250000000000) + (12589:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239782953 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059944161 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12589:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12589:ℚ)^(-2:ℤ) : ℝ) = ((12589:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1504 : ((((1808959157 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12601, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12589 < q → q < 12601 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12601).mp (by decide +kernel))) hgap
  have hprev := s2L_1503
  have hrat : ((1808959157 : ℚ) / 4000000000) ≤ ((452239782953 : ℚ) / 1000000000000) + (12601:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((1808959157 : ℚ) / 4000000000) : ℚ) : ℝ) ≤ ((((452239782953 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12601:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12601:ℚ)^(-2:ℤ) : ℝ) = ((12601:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1505 : ((((452239795537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12611, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12601 < q → q < 12611 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12611).mp (by decide +kernel))) hgap
  have hprev := s2L_1504
  have hrat : ((452239795537 : ℚ) / 1000000000000) ≤ ((1808959157 : ℚ) / 4000000000) + (12611:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239795537 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((1808959157 : ℚ) / 4000000000) : ℚ) : ℝ) + ((12611:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12611:ℚ)^(-2:ℤ) : ℝ) = ((12611:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1506 : ((((226119900911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12613, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12611 < q → q < 12613 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12613).mp (by decide +kernel))) hgap
  have hprev := s2L_1505
  have hrat : ((226119900911 : ℚ) / 500000000000) ≤ ((452239795537 : ℚ) / 1000000000000) + (12613:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119900911 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239795537 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12613:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12613:ℚ)^(-2:ℤ) : ℝ) = ((12613:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1507 : ((((452239808101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12619, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12613 < q → q < 12619 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12619).mp (by decide +kernel))) hgap
  have hprev := s2L_1506
  have hrat : ((452239808101 : ℚ) / 1000000000000) ≤ ((226119900911 : ℚ) / 500000000000) + (12619:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239808101 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119900911 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12619:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12619:ℚ)^(-2:ℤ) : ℝ) = ((12619:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1508 : ((((226119907181 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12637, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12619 < q → q < 12637 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12637).mp (by decide +kernel))) hgap
  have hprev := s2L_1507
  have hrat : ((226119907181 : ℚ) / 500000000000) ≤ ((452239808101 : ℚ) / 1000000000000) + (12637:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119907181 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239808101 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12637:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12637:ℚ)^(-2:ℤ) : ℝ) = ((12637:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1509 : ((((22611991031 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12641, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12637 < q → q < 12641 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12641).mp (by decide +kernel))) hgap
  have hprev := s2L_1508
  have hrat : ((22611991031 : ℚ) / 50000000000) ≤ ((226119907181 : ℚ) / 500000000000) + (12641:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22611991031 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226119907181 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12641:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12641:ℚ)^(-2:ℤ) : ℝ) = ((12641:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1510 : ((((56529978359 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12647, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12641 < q → q < 12647 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12647).mp (by decide +kernel))) hgap
  have hprev := s2L_1509
  have hrat : ((56529978359 : ℚ) / 125000000000) ≤ ((22611991031 : ℚ) / 50000000000) + (12647:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56529978359 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((22611991031 : ℚ) / 50000000000) : ℚ) : ℝ) + ((12647:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12647:ℚ)^(-2:ℤ) : ℝ) = ((12647:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1511 : ((((226119916559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12653, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12647 < q → q < 12653 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12653).mp (by decide +kernel))) hgap
  have hprev := s2L_1510
  have hrat : ((226119916559 : ℚ) / 500000000000) ≤ ((56529978359 : ℚ) / 125000000000) + (12653:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119916559 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((56529978359 : ℚ) / 125000000000) : ℚ) : ℝ) + ((12653:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12653:ℚ)^(-2:ℤ) : ℝ) = ((12653:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1512 : ((((226119919679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12659, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12653 < q → q < 12659 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12659).mp (by decide +kernel))) hgap
  have hprev := s2L_1511
  have hrat : ((226119919679 : ℚ) / 500000000000) ≤ ((226119916559 : ℚ) / 500000000000) + (12659:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119919679 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119916559 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12659:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12659:ℚ)^(-2:ℤ) : ℝ) = ((12659:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1513 : ((((226119922793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12671, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12659 < q → q < 12671 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12671).mp (by decide +kernel))) hgap
  have hprev := s2L_1512
  have hrat : ((226119922793 : ℚ) / 500000000000) ≤ ((226119919679 : ℚ) / 500000000000) + (12671:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119922793 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226119919679 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12671:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12671:ℚ)^(-2:ℤ) : ℝ) = ((12671:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1514 : ((((113059962949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12689, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12671 < q → q < 12689 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12689).mp (by decide +kernel))) hgap
  have hprev := s2L_1513
  have hrat : ((113059962949 : ℚ) / 250000000000) ≤ ((226119922793 : ℚ) / 500000000000) + (12689:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059962949 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119922793 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12689:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12689:ℚ)^(-2:ℤ) : ℝ) = ((12689:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1515 : ((((226119928999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12697, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12689 < q → q < 12697 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12697).mp (by decide +kernel))) hgap
  have hprev := s2L_1514
  have hrat : ((226119928999 : ℚ) / 500000000000) ≤ ((113059962949 : ℚ) / 250000000000) + (12697:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119928999 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113059962949 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12697:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12697:ℚ)^(-2:ℤ) : ℝ) = ((12697:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1516 : ((((90447972839 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12703, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12697 < q → q < 12703 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12703).mp (by decide +kernel))) hgap
  have hprev := s2L_1515
  have hrat : ((90447972839 : ℚ) / 200000000000) ≤ ((226119928999 : ℚ) / 500000000000) + (12703:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447972839 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((226119928999 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12703:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12703:ℚ)^(-2:ℤ) : ℝ) = ((12703:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1517 : ((((226119935191 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12713, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12703 < q → q < 12713 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12713).mp (by decide +kernel))) hgap
  have hprev := s2L_1516
  have hrat : ((226119935191 : ℚ) / 500000000000) ≤ ((90447972839 : ℚ) / 200000000000) + (12713:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119935191 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90447972839 : ℚ) / 200000000000) : ℚ) : ℝ) + ((12713:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12713:ℚ)^(-2:ℤ) : ℝ) = ((12713:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1518 : ((((452239876561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12721, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12713 < q → q < 12721 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12721).mp (by decide +kernel))) hgap
  have hprev := s2L_1517
  have hrat : ((452239876561 : ℚ) / 1000000000000) ≤ ((226119935191 : ℚ) / 500000000000) + (12721:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239876561 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119935191 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12721:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12721:ℚ)^(-2:ℤ) : ℝ) = ((12721:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1519 : ((((452239882723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12739, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12721 < q → q < 12739 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12739).mp (by decide +kernel))) hgap
  have hprev := s2L_1518
  have hrat : ((452239882723 : ℚ) / 1000000000000) ≤ ((452239876561 : ℚ) / 1000000000000) + (12739:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239882723 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239876561 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12739:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12739:ℚ)^(-2:ℤ) : ℝ) = ((12739:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1520 : ((((452239888881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12743, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12739 < q → q < 12743 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12743).mp (by decide +kernel))) hgap
  have hprev := s2L_1519
  have hrat : ((452239888881 : ℚ) / 1000000000000) ≤ ((452239882723 : ℚ) / 1000000000000) + (12743:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239888881 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239882723 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12743:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12743:ℚ)^(-2:ℤ) : ℝ) = ((12743:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1521 : ((((18089595801 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12757, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12743 < q → q < 12757 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12757).mp (by decide +kernel))) hgap
  have hprev := s2L_1520
  have hrat : ((18089595801 : ℚ) / 40000000000) ≤ ((452239888881 : ℚ) / 1000000000000) + (12757:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089595801 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452239888881 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12757:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12757:ℚ)^(-2:ℤ) : ℝ) = ((12757:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1522 : ((((452239901163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12763, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12757 < q → q < 12763 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12763).mp (by decide +kernel))) hgap
  have hprev := s2L_1521
  have hrat : ((452239901163 : ℚ) / 1000000000000) ≤ ((18089595801 : ℚ) / 40000000000) + (12763:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239901163 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089595801 : ℚ) / 40000000000) : ℚ) : ℝ) + ((12763:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12763:ℚ)^(-2:ℤ) : ℝ) = ((12763:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1523 : ((((113059976821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12781, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12763 < q → q < 12781 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12781).mp (by decide +kernel))) hgap
  have hprev := s2L_1522
  have hrat : ((113059976821 : ℚ) / 250000000000) ≤ ((452239901163 : ℚ) / 1000000000000) + (12781:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059976821 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452239901163 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12781:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12781:ℚ)^(-2:ℤ) : ℝ) = ((12781:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1524 : ((((113059978349 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12791, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12781 < q → q < 12791 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12791).mp (by decide +kernel))) hgap
  have hprev := s2L_1523
  have hrat : ((113059978349 : ℚ) / 250000000000) ≤ ((113059976821 : ℚ) / 250000000000) + (12791:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059978349 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((113059976821 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12791:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12791:ℚ)^(-2:ℤ) : ℝ) = ((12791:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1525 : ((((904479839 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12799, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12791 < q → q < 12799 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12799).mp (by decide +kernel))) hgap
  have hprev := s2L_1524
  have hrat : ((904479839 : ℚ) / 2000000000) ≤ ((113059978349 : ℚ) / 250000000000) + (12799:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((904479839 : ℚ) / 2000000000) : ℚ) : ℝ) ≤ ((((113059978349 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12799:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12799:ℚ)^(-2:ℤ) : ℝ) = ((12799:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1526 : ((((226119962797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12809, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12799 < q → q < 12809 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12809).mp (by decide +kernel))) hgap
  have hprev := s2L_1525
  have hrat : ((226119962797 : ℚ) / 500000000000) ≤ ((904479839 : ℚ) / 2000000000) + (12809:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119962797 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((904479839 : ℚ) / 2000000000) : ℚ) : ℝ) + ((12809:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12809:ℚ)^(-2:ℤ) : ℝ) = ((12809:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1527 : ((((452239931677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12821, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12809 < q → q < 12821 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12821).mp (by decide +kernel))) hgap
  have hprev := s2L_1526
  have hrat : ((452239931677 : ℚ) / 1000000000000) ≤ ((226119962797 : ℚ) / 500000000000) + (12821:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239931677 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119962797 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12821:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12821:ℚ)^(-2:ℤ) : ℝ) = ((12821:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1528 : ((((226119968879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12823, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12821 < q → q < 12823 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12823).mp (by decide +kernel))) hgap
  have hprev := s2L_1527
  have hrat : ((226119968879 : ℚ) / 500000000000) ≤ ((452239931677 : ℚ) / 1000000000000) + (12823:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119968879 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239931677 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12823:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12823:ℚ)^(-2:ℤ) : ℝ) = ((12823:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1529 : ((((452239943833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12829, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12823 < q → q < 12829 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12829).mp (by decide +kernel))) hgap
  have hprev := s2L_1528
  have hrat : ((452239943833 : ℚ) / 1000000000000) ≤ ((226119968879 : ℚ) / 500000000000) + (12829:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239943833 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226119968879 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12829:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12829:ℚ)^(-2:ℤ) : ℝ) = ((12829:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1530 : ((((452239949897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12841, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12829 < q → q < 12841 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12841).mp (by decide +kernel))) hgap
  have hprev := s2L_1529
  have hrat : ((452239949897 : ℚ) / 1000000000000) ≤ ((452239943833 : ℚ) / 1000000000000) + (12841:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239949897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452239943833 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12841:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12841:ℚ)^(-2:ℤ) : ℝ) = ((12841:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1531 : ((((9044799119 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12853, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12841 < q → q < 12853 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12853).mp (by decide +kernel))) hgap
  have hprev := s2L_1530
  have hrat : ((9044799119 : ℚ) / 20000000000) ≤ ((452239949897 : ℚ) / 1000000000000) + (12853:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044799119 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452239949897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12853:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12853:ℚ)^(-2:ℤ) : ℝ) = ((12853:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1532 : ((((452239961969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12889, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12853 < q → q < 12889 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12889).mp (by decide +kernel))) hgap
  have hprev := s2L_1531
  have hrat : ((452239961969 : ℚ) / 1000000000000) ≤ ((9044799119 : ℚ) / 20000000000) + (12889:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239961969 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044799119 : ℚ) / 20000000000) : ℚ) : ℝ) + ((12889:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12889:ℚ)^(-2:ℤ) : ℝ) = ((12889:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1533 : ((((28264997999 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12893, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12889 < q → q < 12893 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12893).mp (by decide +kernel))) hgap
  have hprev := s2L_1532
  have hrat : ((28264997999 : ℚ) / 62500000000) ≤ ((452239961969 : ℚ) / 1000000000000) + (12893:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((28264997999 : ℚ) / 62500000000) : ℚ) : ℝ) ≤ ((((452239961969 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12893:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12893:ℚ)^(-2:ℤ) : ℝ) = ((12893:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1534 : ((((226119986997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12899, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12893 < q → q < 12899 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12899).mp (by decide +kernel))) hgap
  have hprev := s2L_1533
  have hrat : ((226119986997 : ℚ) / 500000000000) ≤ ((28264997999 : ℚ) / 62500000000) + (12899:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226119986997 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((28264997999 : ℚ) / 62500000000) : ℚ) : ℝ) + ((12899:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12899:ℚ)^(-2:ℤ) : ℝ) = ((12899:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1535 : ((((113059994999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12907, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12899 < q → q < 12907 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12907).mp (by decide +kernel))) hgap
  have hprev := s2L_1534
  have hrat : ((113059994999 : ℚ) / 250000000000) ≤ ((226119986997 : ℚ) / 500000000000) + (12907:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059994999 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((226119986997 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12907:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12907:ℚ)^(-2:ℤ) : ℝ) = ((12907:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1536 : ((((90447997199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12911, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12907 < q → q < 12911 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12911).mp (by decide +kernel))) hgap
  have hprev := s2L_1535
  have hrat : ((90447997199 : ℚ) / 200000000000) ≤ ((113059994999 : ℚ) / 250000000000) + (12911:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90447997199 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((113059994999 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12911:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12911:ℚ)^(-2:ℤ) : ℝ) = ((12911:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1537 : ((((113059997997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12917, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12911 < q → q < 12917 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12917).mp (by decide +kernel))) hgap
  have hprev := s2L_1536
  have hrat : ((113059997997 : ℚ) / 250000000000) ≤ ((90447997199 : ℚ) / 200000000000) + (12917:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113059997997 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90447997199 : ℚ) / 200000000000) : ℚ) : ℝ) + ((12917:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12917:ℚ)^(-2:ℤ) : ℝ) = ((12917:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1538 : ((((452239997979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12919, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12917 < q → q < 12919 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12919).mp (by decide +kernel))) hgap
  have hprev := s2L_1537
  have hrat : ((452239997979 : ℚ) / 1000000000000) ≤ ((113059997997 : ℚ) / 250000000000) + (12919:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452239997979 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113059997997 : ℚ) / 250000000000) : ℚ) : ℝ) + ((12919:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12919:ℚ)^(-2:ℤ) : ℝ) = ((12919:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1539 : ((((226120001983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12923, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12919 < q → q < 12923 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12923).mp (by decide +kernel))) hgap
  have hprev := s2L_1538
  have hrat : ((226120001983 : ℚ) / 500000000000) ≤ ((452239997979 : ℚ) / 1000000000000) + (12923:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120001983 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452239997979 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12923:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12923:ℚ)^(-2:ℤ) : ℝ) = ((12923:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1540 : ((((452240009937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12941, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12923 < q → q < 12941 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12941).mp (by decide +kernel))) hgap
  have hprev := s2L_1539
  have hrat : ((452240009937 : ℚ) / 1000000000000) ≤ ((226120001983 : ℚ) / 500000000000) + (12941:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240009937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120001983 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12941:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12941:ℚ)^(-2:ℤ) : ℝ) = ((12941:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1541 : ((((452240015897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12953, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12941 < q → q < 12953 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12953).mp (by decide +kernel))) hgap
  have hprev := s2L_1540
  have hrat : ((452240015897 : ℚ) / 1000000000000) ≤ ((452240009937 : ℚ) / 1000000000000) + (12953:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240015897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240009937 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12953:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12953:ℚ)^(-2:ℤ) : ℝ) = ((12953:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1542 : ((((452240021851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12959, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12953 < q → q < 12959 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12959).mp (by decide +kernel))) hgap
  have hprev := s2L_1541
  have hrat : ((452240021851 : ℚ) / 1000000000000) ≤ ((452240015897 : ℚ) / 1000000000000) + (12959:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240021851 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240015897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12959:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12959:ℚ)^(-2:ℤ) : ℝ) = ((12959:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1543 : ((((226120013899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12967, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12959 < q → q < 12967 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12967).mp (by decide +kernel))) hgap
  have hprev := s2L_1542
  have hrat : ((226120013899 : ℚ) / 500000000000) ≤ ((452240021851 : ℚ) / 1000000000000) + (12967:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120013899 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240021851 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12967:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12967:ℚ)^(-2:ℤ) : ℝ) = ((12967:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1544 : ((((452240033739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12973, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12967 < q → q < 12973 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12973).mp (by decide +kernel))) hgap
  have hprev := s2L_1543
  have hrat : ((452240033739 : ℚ) / 1000000000000) ≤ ((226120013899 : ℚ) / 500000000000) + (12973:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240033739 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120013899 : ℚ) / 500000000000) : ℚ) : ℝ) + ((12973:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12973:ℚ)^(-2:ℤ) : ℝ) = ((12973:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1545 : ((((18089601587 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12979, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12973 < q → q < 12979 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12979).mp (by decide +kernel))) hgap
  have hprev := s2L_1544
  have hrat : ((18089601587 : ℚ) / 40000000000) ≤ ((452240033739 : ℚ) / 1000000000000) + (12979:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089601587 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452240033739 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((12979:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12979:ℚ)^(-2:ℤ) : ℝ) = ((12979:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1546 : ((((452240045607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 12983, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12979 < q → q < 12983 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 12983).mp (by decide +kernel))) hgap
  have hprev := s2L_1545
  have hrat : ((452240045607 : ℚ) / 1000000000000) ≤ ((18089601587 : ℚ) / 40000000000) + (12983:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240045607 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089601587 : ℚ) / 40000000000) : ℚ) : ℝ) + ((12983:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((12983:ℚ)^(-2:ℤ) : ℝ) = ((12983:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1547 : ((((452240051523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13001, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 12983 < q → q < 13001 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13001).mp (by decide +kernel))) hgap
  have hprev := s2L_1546
  have hrat : ((452240051523 : ℚ) / 1000000000000) ≤ ((452240045607 : ℚ) / 1000000000000) + (13001:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240051523 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240045607 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13001:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13001:ℚ)^(-2:ℤ) : ℝ) = ((13001:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1548 : ((((452240057437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13003, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13001 < q → q < 13003 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13003).mp (by decide +kernel))) hgap
  have hprev := s2L_1547
  have hrat : ((452240057437 : ℚ) / 1000000000000) ≤ ((452240051523 : ℚ) / 1000000000000) + (13003:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240057437 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240051523 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13003:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13003:ℚ)^(-2:ℤ) : ℝ) = ((13003:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1549 : ((((452240063347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13007, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13003 < q → q < 13007 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13007).mp (by decide +kernel))) hgap
  have hprev := s2L_1548
  have hrat : ((452240063347 : ℚ) / 1000000000000) ≤ ((452240057437 : ℚ) / 1000000000000) + (13007:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240063347 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240057437 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13007:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13007:ℚ)^(-2:ℤ) : ℝ) = ((13007:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1550 : ((((90448013851 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13009, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13007 < q → q < 13009 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13009).mp (by decide +kernel))) hgap
  have hprev := s2L_1549
  have hrat : ((90448013851 : ℚ) / 200000000000) ≤ ((452240063347 : ℚ) / 1000000000000) + (13009:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448013851 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((452240063347 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13009:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13009:ℚ)^(-2:ℤ) : ℝ) = ((13009:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1551 : ((((226120037571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13033, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13009 < q → q < 13033 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13033).mp (by decide +kernel))) hgap
  have hprev := s2L_1550
  have hrat : ((226120037571 : ℚ) / 500000000000) ≤ ((90448013851 : ℚ) / 200000000000) + (13033:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120037571 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((90448013851 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13033:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13033:ℚ)^(-2:ℤ) : ℝ) = ((13033:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1552 : ((((18089603241 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13037, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13033 < q → q < 13037 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13037).mp (by decide +kernel))) hgap
  have hprev := s2L_1551
  have hrat : ((18089603241 : ℚ) / 40000000000) ≤ ((226120037571 : ℚ) / 500000000000) + (13037:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089603241 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((226120037571 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13037:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13037:ℚ)^(-2:ℤ) : ℝ) = ((13037:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1553 : ((((452240086903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13043, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13037 < q → q < 13043 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13043).mp (by decide +kernel))) hgap
  have hprev := s2L_1552
  have hrat : ((452240086903 : ℚ) / 1000000000000) ≤ ((18089603241 : ℚ) / 40000000000) + (13043:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240086903 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((18089603241 : ℚ) / 40000000000) : ℚ) : ℝ) + ((13043:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13043:ℚ)^(-2:ℤ) : ℝ) = ((13043:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1554 : ((((18089603711 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13049, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13043 < q → q < 13049 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13049).mp (by decide +kernel))) hgap
  have hprev := s2L_1553
  have hrat : ((18089603711 : ℚ) / 40000000000) ≤ ((452240086903 : ℚ) / 1000000000000) + (13049:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((18089603711 : ℚ) / 40000000000) : ℚ) : ℝ) ≤ ((((452240086903 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13049:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13049:ℚ)^(-2:ℤ) : ℝ) = ((13049:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1555 : ((((90448019727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13063, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13049 < q → q < 13063 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13063).mp (by decide +kernel))) hgap
  have hprev := s2L_1554
  have hrat : ((90448019727 : ℚ) / 200000000000) ≤ ((18089603711 : ℚ) / 40000000000) + (13063:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448019727 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((18089603711 : ℚ) / 40000000000) : ℚ) : ℝ) + ((13063:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13063:ℚ)^(-2:ℤ) : ℝ) = ((13063:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1556 : ((((113060026117 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13093, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13063 < q → q < 13093 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13093).mp (by decide +kernel))) hgap
  have hprev := s2L_1555
  have hrat : ((113060026117 : ℚ) / 250000000000) ≤ ((90448019727 : ℚ) / 200000000000) + (13093:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060026117 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((90448019727 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13093:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13093:ℚ)^(-2:ℤ) : ℝ) = ((13093:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1557 : ((((56530013787 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13099, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13093 < q → q < 13099 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13099).mp (by decide +kernel))) hgap
  have hprev := s2L_1556
  have hrat : ((56530013787 : ℚ) / 125000000000) ≤ ((113060026117 : ℚ) / 250000000000) + (13099:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530013787 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((113060026117 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13099:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13099:ℚ)^(-2:ℤ) : ℝ) = ((13099:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1558 : ((((11306002903 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13103, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13099 < q → q < 13103 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13103).mp (by decide +kernel))) hgap
  have hprev := s2L_1557
  have hrat : ((11306002903 : ℚ) / 25000000000) ≤ ((56530013787 : ℚ) / 125000000000) + (13103:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((11306002903 : ℚ) / 25000000000) : ℚ) : ℝ) ≤ ((((56530013787 : ℚ) / 125000000000) : ℚ) : ℝ) + ((13103:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13103:ℚ)^(-2:ℤ) : ℝ) = ((13103:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1559 : ((((452240121939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13109, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13103 < q → q < 13109 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13109).mp (by decide +kernel))) hgap
  have hprev := s2L_1558
  have hrat : ((452240121939 : ℚ) / 1000000000000) ≤ ((11306002903 : ℚ) / 25000000000) + (13109:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240121939 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((11306002903 : ℚ) / 25000000000) : ℚ) : ℝ) + ((13109:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13109:ℚ)^(-2:ℤ) : ℝ) = ((13109:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1560 : ((((452240127747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13121, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13109 < q → q < 13121 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13121).mp (by decide +kernel))) hgap
  have hprev := s2L_1559
  have hrat : ((452240127747 : ℚ) / 1000000000000) ≤ ((452240121939 : ℚ) / 1000000000000) + (13121:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240127747 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240121939 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13121:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13121:ℚ)^(-2:ℤ) : ℝ) = ((13121:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1561 : ((((9044802671 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13127, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13121 < q → q < 13127 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13127).mp (by decide +kernel))) hgap
  have hprev := s2L_1560
  have hrat : ((9044802671 : ℚ) / 20000000000) ≤ ((452240127747 : ℚ) / 1000000000000) + (13127:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044802671 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((452240127747 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13127:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13127:ℚ)^(-2:ℤ) : ℝ) = ((13127:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1562 : ((((90448027867 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13147, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13127 < q → q < 13147 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13147).mp (by decide +kernel))) hgap
  have hprev := s2L_1561
  have hrat : ((90448027867 : ℚ) / 200000000000) ≤ ((9044802671 : ℚ) / 20000000000) + (13147:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448027867 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((9044802671 : ℚ) / 20000000000) : ℚ) : ℝ) + ((13147:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13147:ℚ)^(-2:ℤ) : ℝ) = ((13147:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1563 : ((((452240145117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13151, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13147 < q → q < 13151 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13151).mp (by decide +kernel))) hgap
  have hprev := s2L_1562
  have hrat : ((452240145117 : ℚ) / 1000000000000) ≤ ((90448027867 : ℚ) / 200000000000) + (13151:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240145117 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448027867 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13151:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13151:ℚ)^(-2:ℤ) : ℝ) = ((13151:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1564 : ((((113060037723 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13159, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13151 < q → q < 13159 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13159).mp (by decide +kernel))) hgap
  have hprev := s2L_1563
  have hrat : ((113060037723 : ℚ) / 250000000000) ≤ ((452240145117 : ℚ) / 1000000000000) + (13159:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060037723 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240145117 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13159:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13159:ℚ)^(-2:ℤ) : ℝ) = ((13159:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1565 : ((((452240156663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13163, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13159 < q → q < 13163 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13163).mp (by decide +kernel))) hgap
  have hprev := s2L_1564
  have hrat : ((452240156663 : ℚ) / 1000000000000) ≤ ((113060037723 : ℚ) / 250000000000) + (13163:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240156663 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060037723 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13163:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13163:ℚ)^(-2:ℤ) : ℝ) = ((13163:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1566 : ((((452240162427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13171, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13163 < q → q < 13171 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13171).mp (by decide +kernel))) hgap
  have hprev := s2L_1565
  have hrat : ((452240162427 : ℚ) / 1000000000000) ≤ ((452240156663 : ℚ) / 1000000000000) + (13171:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240162427 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240156663 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13171:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13171:ℚ)^(-2:ℤ) : ℝ) = ((13171:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1567 : ((((226120084093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13177, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13171 < q → q < 13177 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13177).mp (by decide +kernel))) hgap
  have hprev := s2L_1566
  have hrat : ((226120084093 : ℚ) / 500000000000) ≤ ((452240162427 : ℚ) / 1000000000000) + (13177:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120084093 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240162427 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13177:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13177:ℚ)^(-2:ℤ) : ℝ) = ((13177:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1568 : ((((22612008697 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13183, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13177 < q → q < 13183 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13183).mp (by decide +kernel))) hgap
  have hprev := s2L_1567
  have hrat : ((22612008697 : ℚ) / 50000000000) ≤ ((226120084093 : ℚ) / 500000000000) + (13183:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612008697 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226120084093 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13183:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13183:ℚ)^(-2:ℤ) : ℝ) = ((13183:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1569 : ((((45224017969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13187, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13183 < q → q < 13187 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13187).mp (by decide +kernel))) hgap
  have hprev := s2L_1568
  have hrat : ((45224017969 : ℚ) / 100000000000) ≤ ((22612008697 : ℚ) / 50000000000) + (13187:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((45224017969 : ℚ) / 100000000000) : ℚ) : ℝ) ≤ ((((22612008697 : ℚ) / 50000000000) : ℚ) : ℝ) + ((13187:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13187:ℚ)^(-2:ℤ) : ℝ) = ((13187:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1570 : ((((226120092707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13217, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13187 < q → q < 13217 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13217).mp (by decide +kernel))) hgap
  have hprev := s2L_1569
  have hrat : ((226120092707 : ℚ) / 500000000000) ≤ ((45224017969 : ℚ) / 100000000000) + (13217:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120092707 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((45224017969 : ℚ) / 100000000000) : ℚ) : ℝ) + ((13217:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13217:ℚ)^(-2:ℤ) : ℝ) = ((13217:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1571 : ((((14132505973 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13219, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13217 < q → q < 13219 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13219).mp (by decide +kernel))) hgap
  have hprev := s2L_1570
  have hrat : ((14132505973 : ℚ) / 31250000000) ≤ ((226120092707 : ℚ) / 500000000000) + (13219:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132505973 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226120092707 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13219:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13219:ℚ)^(-2:ℤ) : ℝ) = ((13219:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1572 : ((((9044803937 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13229, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13219 < q → q < 13229 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13229).mp (by decide +kernel))) hgap
  have hprev := s2L_1571
  have hrat : ((9044803937 : ℚ) / 20000000000) ≤ ((14132505973 : ℚ) / 31250000000) + (13229:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044803937 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((14132505973 : ℚ) / 31250000000) : ℚ) : ℝ) + ((13229:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13229:ℚ)^(-2:ℤ) : ℝ) = ((13229:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1573 : ((((452240202553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13241, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13229 < q → q < 13241 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13241).mp (by decide +kernel))) hgap
  have hprev := s2L_1572
  have hrat : ((452240202553 : ℚ) / 1000000000000) ≤ ((9044803937 : ℚ) / 20000000000) + (13241:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240202553 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((9044803937 : ℚ) / 20000000000) : ℚ) : ℝ) + ((13241:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13241:ℚ)^(-2:ℤ) : ℝ) = ((13241:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1574 : ((((452240208249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13249, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13241 < q → q < 13249 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13249).mp (by decide +kernel))) hgap
  have hprev := s2L_1573
  have hrat : ((452240208249 : ℚ) / 1000000000000) ≤ ((452240202553 : ℚ) / 1000000000000) + (13249:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240208249 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240202553 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13249:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13249:ℚ)^(-2:ℤ) : ℝ) = ((13249:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1575 : ((((452240213937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13259, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13249 < q → q < 13259 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13259).mp (by decide +kernel))) hgap
  have hprev := s2L_1574
  have hrat : ((452240213937 : ℚ) / 1000000000000) ≤ ((452240208249 : ℚ) / 1000000000000) + (13259:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240213937 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240208249 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13259:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13259:ℚ)^(-2:ℤ) : ℝ) = ((13259:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1576 : ((((226120109809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13267, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13259 < q → q < 13267 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13267).mp (by decide +kernel))) hgap
  have hprev := s2L_1575
  have hrat : ((226120109809 : ℚ) / 500000000000) ≤ ((452240213937 : ℚ) / 1000000000000) + (13267:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120109809 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240213937 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13267:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13267:ℚ)^(-2:ℤ) : ℝ) = ((13267:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1577 : ((((226120112639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13291, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13267 < q → q < 13291 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13291).mp (by decide +kernel))) hgap
  have hprev := s2L_1576
  have hrat : ((226120112639 : ℚ) / 500000000000) ≤ ((226120109809 : ℚ) / 500000000000) + (13291:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120112639 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120109809 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13291:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13291:ℚ)^(-2:ℤ) : ℝ) = ((13291:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1578 : ((((452240230933 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13297, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13291 < q → q < 13297 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13297).mp (by decide +kernel))) hgap
  have hprev := s2L_1577
  have hrat : ((452240230933 : ℚ) / 1000000000000) ≤ ((226120112639 : ℚ) / 500000000000) + (13297:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240230933 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120112639 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13297:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13297:ℚ)^(-2:ℤ) : ℝ) = ((13297:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1579 : ((((226120118289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13309, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13297 < q → q < 13309 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13309).mp (by decide +kernel))) hgap
  have hprev := s2L_1578
  have hrat : ((226120118289 : ℚ) / 500000000000) ≤ ((452240230933 : ℚ) / 1000000000000) + (13309:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120118289 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240230933 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13309:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13309:ℚ)^(-2:ℤ) : ℝ) = ((13309:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1580 : ((((22612012111 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13313, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13309 < q → q < 13313 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13313).mp (by decide +kernel))) hgap
  have hprev := s2L_1579
  have hrat : ((22612012111 : ℚ) / 50000000000) ≤ ((226120118289 : ℚ) / 500000000000) + (13313:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((22612012111 : ℚ) / 50000000000) : ℚ) : ℝ) ≤ ((((226120118289 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13313:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13313:ℚ)^(-2:ℤ) : ℝ) = ((13313:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1581 : ((((9044804957 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13327, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13313 < q → q < 13327 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13327).mp (by decide +kernel))) hgap
  have hprev := s2L_1580
  have hrat : ((9044804957 : ℚ) / 20000000000) ≤ ((22612012111 : ℚ) / 50000000000) + (13327:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((9044804957 : ℚ) / 20000000000) : ℚ) : ℝ) ≤ ((((22612012111 : ℚ) / 50000000000) : ℚ) : ℝ) + ((13327:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13327:ℚ)^(-2:ℤ) : ℝ) = ((13327:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1582 : ((((113060063369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13331, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13327 < q → q < 13331 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13331).mp (by decide +kernel))) hgap
  have hprev := s2L_1581
  have hrat : ((113060063369 : ℚ) / 250000000000) ≤ ((9044804957 : ℚ) / 20000000000) + (13331:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060063369 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((9044804957 : ℚ) / 20000000000) : ℚ) : ℝ) + ((13331:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13331:ℚ)^(-2:ℤ) : ℝ) = ((13331:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1583 : ((((452240259097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13337, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13331 < q → q < 13337 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13337).mp (by decide +kernel))) hgap
  have hprev := s2L_1582
  have hrat : ((452240259097 : ℚ) / 1000000000000) ≤ ((113060063369 : ℚ) / 250000000000) + (13337:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240259097 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((113060063369 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13337:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13337:ℚ)^(-2:ℤ) : ℝ) = ((13337:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1584 : ((((452240264717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13339, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13337 < q → q < 13339 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13339).mp (by decide +kernel))) hgap
  have hprev := s2L_1583
  have hrat : ((452240264717 : ℚ) / 1000000000000) ≤ ((452240259097 : ℚ) / 1000000000000) + (13339:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240264717 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240259097 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13339:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13339:ℚ)^(-2:ℤ) : ℝ) = ((13339:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1585 : ((((452240270313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13367, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13339 < q → q < 13367 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13367).mp (by decide +kernel))) hgap
  have hprev := s2L_1584
  have hrat : ((452240270313 : ℚ) / 1000000000000) ≤ ((452240264717 : ℚ) / 1000000000000) + (13367:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240270313 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240264717 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13367:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13367:ℚ)^(-2:ℤ) : ℝ) = ((13367:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1586 : ((((452240275897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13381, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13367 < q → q < 13381 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13381).mp (by decide +kernel))) hgap
  have hprev := s2L_1585
  have hrat : ((452240275897 : ℚ) / 1000000000000) ≤ ((452240270313 : ℚ) / 1000000000000) + (13381:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240275897 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((452240270313 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13381:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13381:ℚ)^(-2:ℤ) : ℝ) = ((13381:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1587 : ((((113060070367 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13397, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13381 < q → q < 13397 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13397).mp (by decide +kernel))) hgap
  have hprev := s2L_1586
  have hrat : ((113060070367 : ℚ) / 250000000000) ≤ ((452240275897 : ℚ) / 1000000000000) + (13397:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((113060070367 : ℚ) / 250000000000) : ℚ) : ℝ) ≤ ((((452240275897 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13397:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13397:ℚ)^(-2:ℤ) : ℝ) = ((13397:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1588 : ((((226120143519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13399, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13397 < q → q < 13399 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13399).mp (by decide +kernel))) hgap
  have hprev := s2L_1587
  have hrat : ((226120143519 : ℚ) / 500000000000) ≤ ((113060070367 : ℚ) / 250000000000) + (13399:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120143519 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((113060070367 : ℚ) / 250000000000) : ℚ) : ℝ) + ((13399:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13399:ℚ)^(-2:ℤ) : ℝ) = ((13399:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1589 : ((((226120146299 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13411, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13399 < q → q < 13411 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13411).mp (by decide +kernel))) hgap
  have hprev := s2L_1588
  have hrat : ((226120146299 : ℚ) / 500000000000) ≤ ((226120143519 : ℚ) / 500000000000) + (13411:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120146299 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120143519 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13411:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13411:ℚ)^(-2:ℤ) : ℝ) = ((13411:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1590 : ((((452240298153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13417, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13411 < q → q < 13417 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13417).mp (by decide +kernel))) hgap
  have hprev := s2L_1589
  have hrat : ((452240298153 : ℚ) / 1000000000000) ≤ ((226120146299 : ℚ) / 500000000000) + (13417:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240298153 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120146299 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13417:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13417:ℚ)^(-2:ℤ) : ℝ) = ((13417:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1591 : ((((56530037963 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13421, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13417 < q → q < 13421 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13421).mp (by decide +kernel))) hgap
  have hprev := s2L_1590
  have hrat : ((56530037963 : ℚ) / 125000000000) ≤ ((452240298153 : ℚ) / 1000000000000) + (13421:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((56530037963 : ℚ) / 125000000000) : ℚ) : ℝ) ≤ ((((452240298153 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13421:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13421:ℚ)^(-2:ℤ) : ℝ) = ((13421:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1592 : ((((452240309239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13441, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13421 < q → q < 13441 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13441).mp (by decide +kernel))) hgap
  have hprev := s2L_1591
  have hrat : ((452240309239 : ℚ) / 1000000000000) ≤ ((56530037963 : ℚ) / 125000000000) + (13441:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240309239 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((56530037963 : ℚ) / 125000000000) : ℚ) : ℝ) + ((13441:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13441:ℚ)^(-2:ℤ) : ℝ) = ((13441:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1593 : ((((226120157383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13451, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13441 < q → q < 13451 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13451).mp (by decide +kernel))) hgap
  have hprev := s2L_1592
  have hrat : ((226120157383 : ℚ) / 500000000000) ≤ ((452240309239 : ℚ) / 1000000000000) + (13451:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120157383 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240309239 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13451:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13451:ℚ)^(-2:ℤ) : ℝ) = ((13451:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1594 : ((((14132510009 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13457, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13451 < q → q < 13457 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13457).mp (by decide +kernel))) hgap
  have hprev := s2L_1593
  have hrat : ((14132510009 : ℚ) / 31250000000) ≤ ((226120157383 : ℚ) / 500000000000) + (13457:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((14132510009 : ℚ) / 31250000000) : ℚ) : ℝ) ≤ ((((226120157383 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13457:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13457:ℚ)^(-2:ℤ) : ℝ) = ((13457:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1595 : ((((90448065161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13463, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13457 < q → q < 13463 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13463).mp (by decide +kernel))) hgap
  have hprev := s2L_1594
  have hrat : ((90448065161 : ℚ) / 200000000000) ≤ ((14132510009 : ℚ) / 31250000000) + (13463:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((90448065161 : ℚ) / 200000000000) : ℚ) : ℝ) ≤ ((((14132510009 : ℚ) / 31250000000) : ℚ) : ℝ) + ((13463:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13463:ℚ)^(-2:ℤ) : ℝ) = ((13463:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1596 : ((((452240331317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13469, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13463 < q → q < 13469 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13469).mp (by decide +kernel))) hgap
  have hprev := s2L_1595
  have hrat : ((452240331317 : ℚ) / 1000000000000) ≤ ((90448065161 : ℚ) / 200000000000) + (13469:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240331317 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((90448065161 : ℚ) / 200000000000) : ℚ) : ℝ) + ((13469:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13469:ℚ)^(-2:ℤ) : ℝ) = ((13469:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1597 : ((((226120168411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13477, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13469 < q → q < 13477 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13477).mp (by decide +kernel))) hgap
  have hprev := s2L_1596
  have hrat : ((226120168411 : ℚ) / 500000000000) ≤ ((452240331317 : ℚ) / 1000000000000) + (13477:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120168411 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240331317 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13477:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13477:ℚ)^(-2:ℤ) : ℝ) = ((13477:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1598 : ((((452240342319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13487, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13477 < q → q < 13487 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13487).mp (by decide +kernel))) hgap
  have hprev := s2L_1597
  have hrat : ((452240342319 : ℚ) / 1000000000000) ≤ ((226120168411 : ℚ) / 500000000000) + (13487:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((452240342319 : ℚ) / 1000000000000) : ℚ) : ℝ) ≤ ((((226120168411 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13487:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13487:ℚ)^(-2:ℤ) : ℝ) = ((13487:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1599 : ((((226120173903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13499, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13487 < q → q < 13499 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13499).mp (by decide +kernel))) hgap
  have hprev := s2L_1598
  have hrat : ((226120173903 : ℚ) / 500000000000) ≤ ((452240342319 : ℚ) / 1000000000000) + (13499:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120173903 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((452240342319 : ℚ) / 1000000000000) : ℚ) : ℝ) + ((13499:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13499:ℚ)^(-2:ℤ) : ℝ) = ((13499:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1600 : ((((226120176641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13513, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13499 < q → q < 13513 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13513).mp (by decide +kernel))) hgap
  have hprev := s2L_1599
  have hrat : ((226120176641 : ℚ) / 500000000000) ≤ ((226120173903 : ℚ) / 500000000000) + (13513:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((226120176641 : ℚ) / 500000000000) : ℚ) : ℝ) ≤ ((((226120173903 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13513:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13513:ℚ)^(-2:ℤ) : ℝ) = ((13513:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))
lemma s2L_1601 : ((((361792287 : ℚ) / 800000000) : ℚ) : ℝ) ≤ (∑ p ∈ Nat.primesLE 13523, ((p : ℕ) : ℝ) ^ (-2 : ℤ)) := by
  have hgap : ∀ q : ℕ, 13513 < q → q < 13523 → ¬ Nat.Prime q :=
    (Work.RHContract.A.RegionI.steps_basic).1 (by norm_num) (by decide +kernel)
  have hstep := (Work.RHContract.A.RegionI.steps_basic).2.2.2.1 (by norm_num) (((Work.RHContract.RegionI.isP_iff 13523).mp (by decide +kernel))) hgap
  have hprev := s2L_1600
  have hrat : ((361792287 : ℚ) / 800000000) ≤ ((226120176641 : ℚ) / 500000000000) + (13523:ℚ)^(-2:ℤ) := by decide +kernel
  have hcast : ((((361792287 : ℚ) / 800000000) : ℚ) : ℝ) ≤ ((((226120176641 : ℚ) / 500000000000) : ℚ) : ℝ) + ((13523:ℚ)^(-2:ℤ) : ℝ) := by exact_mod_cast hrat
  have hcz : ((13523:ℚ)^(-2:ℤ) : ℝ) = ((13523:ℕ):ℝ)^(-2:ℤ) := by push_cast; ring
  rw [hcz] at hcast
  rw [hstep]
  exact le_trans hcast (add_le_add hprev (le_refl _))

end

end Work.RHContract.RegionI
