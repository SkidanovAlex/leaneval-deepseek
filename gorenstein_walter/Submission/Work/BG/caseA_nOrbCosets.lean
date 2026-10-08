-- The statement `Work.BG.nOrbCosets` proved from the two clean index lemmas
-- `Work.BG.caseA_nOrbIndexDvdSix` / `Work.BG.caseA_nOrbIndexOdd` (proved in
-- `caseA_nOrbIndex.lean`) in place of the `sorry`-based `Work.BG.nOrbIndexDvdSix` /
-- `Work.BG.nOrbIndexOdd`.  Needed by the proof of `Work.BG.caseA`.
import Mathlib
import Submission.Work.BG.nOrbCosets
import Submission.Work.BG.nOrbCosetIndexThree
import Submission.Work.BG.caseA_nOrbIndex

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2

-- (`Work.BG.BGData_isFourGroup` and `Work.BG.BGData_S_comm` are taken from the imported
-- module `Submission.Work.BG.nOrbCosets`; both have `sorry`-free proofs.)
theorem caseA_nOrbCosets {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (hn : D.n = 2) :
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        x ^ 3 ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G)) ∧
    (∀ x ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
      x ∉ Subgroup.centralizer ((D.S : Subgroup G) : Set G) →
      ∀ y ∈ Subgroup.normalizer ((D.S : Subgroup G) : Set G),
        y ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x) ∨
        (∃ c ∈ Subgroup.centralizer ((D.S : Subgroup G) : Set G), y = c * x ^ 2)) := by
  classical
  set V : Subgroup G := (D.S : Subgroup G) with hVdef
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hNdef
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hCdef
  have h4 := BGData_isFourGroup D hn
  have hcard : Nat.card ↥V = 4 := h4.1
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := BGData_S_comm D hn
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (V : Set G)
  have hidx6 : (C.subgroupOf N).index ∣ 6 := caseA_nOrbIndexDvdSix V hcard
  have hodd : Odd ((C.subgroupOf N).index) := caseA_nOrbIndexOdd D.S hcomm
  -- `|N : C|` is odd and divides `6`, hence divides `3`, hence is `1` or `3`.
  have hidx3 : (C.subgroupOf N).index ∣ 3 := by
    have hidx6' : (C.subgroupOf N).index ∣ 2 * 3 := by
      rw [show (2 : ℕ) * 3 = 6 by norm_num]
      exact hidx6
    exact hodd.coprime_two_right.dvd_mul_left.mp hidx6'
  have hcases : (C.subgroupOf N).index = 1 ∨ (C.subgroupOf N).index = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hidx3
  constructor
  · intro x hxN
    have hmem : (⟨x, hxN⟩ : ↥N) ^ 3 ∈ C.subgroupOf N := by
      rcases hcases with h1 | h3
      · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      · rw [← h3]; exact Subgroup.pow_index_mem (C.subgroupOf N) ⟨x, hxN⟩
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  · intro x hxN hxC y hyN
    rcases hcases with h1 | h3
    · left
      have hmem : (⟨y, hyN⟩ : ↥N) ∈ C.subgroupOf N := by
        rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    · have hxN' : (⟨x, hxN⟩ : ↥N) ∉ C.subgroupOf N := by
        intro h
        exact hxC (by simpa using (Subgroup.mem_subgroupOf.mp h))
      rcases nOrbCosetIndexThree (C.subgroupOf N) h3 hxN' ⟨y, hyN⟩ with
        hmem | ⟨c, hc, hce⟩ | ⟨c, hc, hce⟩
      · left
        simpa using (Subgroup.mem_subgroupOf.mp hmem)
      · right; left
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce
      · right; right
        refine ⟨(c : G), Subgroup.mem_subgroupOf.mp hc, ?_⟩
        simpa using congrArg (fun z : ↥N => (z : G)) hce

end Work.BG
