import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.d16_case_a_false
import Submission.Work.DSTR.fittingPiIn_eq_iSup_pCoreIn_prime
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup

namespace Work.CORE3

open Subgroup

/-- `O₃(K)` and the `3'`-part `F_{3'}(K)` of the Fitting subgroup of `K` commute: they are
normal subgroups of `K` (indeed `O₃(K) ◁ K`, and `F_{3'}(K) = O_{3'}(F(K))` is characteristic
in `F(K) ◁ K`), their orders are coprime (`O₃(K)` is a `3`-group and `F_{3'}(K)` is a
`3'`-group), so they are disjoint, and disjoint normal subgroups commute. -/
theorem c1aDirPcommF3 {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ⁅Work.GW2.pCoreIn 3 K, Work.GW2.fittingPiIn ({3}ᶜ) K⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- `F_{3'}(↥K)` is a `3'`-subgroup
  have hBpi : Subgroup.IsPiSubgroup ({3}ᶜ : Set ℕ)
      (Work.GW2.fittingPi ({3}ᶜ) ↥K) :=
    Work.DSTR.FittingPiImg.isPiSubgroup_map
      (Work.DSTR.FittingPiImg.isPiSubgroup_piCore ({3}ᶜ : Set ℕ))
  have hB3 : ¬ 3 ∣ Nat.card ↥(Work.GW2.fittingPi ({3}ᶜ) ↥K) := by
    intro hd
    have hmem : 3 ∈ (Nat.card ↥(Work.GW2.fittingPi ({3}ᶜ) ↥K)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hd, Nat.card_pos.ne'⟩
    exact absurd (hBpi 3 hmem) (by simp)
  -- normality of the two subgroups of `↥K`
  haveI hFn : (Work.GW2.fitting ↥K).Normal := by
    rw [Work.DSTR.FittingPiImg.fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥K
  haveI hBn : (Work.GW2.fittingPi ({3}ᶜ) ↥K).Normal := by
    haveI hchar : (Work.GW2.piCore ({3}ᶜ) ↥(Work.GW2.fitting ↥K)).Characteristic :=
      Work.DSTR.FittingPiImg.piCore_characteristic ({3}ᶜ)
    exact ConjAct.normal_of_characteristic_of_normal
  haveI hAn : (Work.GW2.pCore 3 ↥K).Normal := Work.GW2.pCore_normal 3 ↥K
  -- the two subgroups are disjoint (their orders are coprime)
  have hdisj : Disjoint (Work.GW2.pCore 3 ↥K) (Work.GW2.fittingPi ({3}ᶜ) ↥K) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨n, hn⟩ :=
      (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥K) (p := 3)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hB3)
  -- hence the commutator is trivial inside `↥K`
  have hAB : ⁅(Work.GW2.pCore 3 ↥K), (Work.GW2.fittingPi ({3}ᶜ) ↥K)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_of_disjoint hdisj
  -- transport along the inclusion `↥K ↪ G`
  show ⁅(Work.GW2.pCore 3 ↥K).map K.subtype,
      (Work.GW2.fittingPi ({3}ᶜ) ↥K).map K.subtype⁆ = ⊥
  rw [← Subgroup.map_commutator, hAB, Subgroup.map_bot]

end Work.CORE3
