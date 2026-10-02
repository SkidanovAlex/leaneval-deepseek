/-
# `ELAssembly` — the cut points of the arms `B` and `C`

`ELNest` proves the cut-point facts for the arm `A` (`Work.ELNest.cut_mem_A`,
`Work.ELNest.cut_unique_A`); the consumer `Work.EL.B2Data` needs them for **all three** arms,
indexed by `Work.EL.ArmIdx`.  The proofs are the same argument with the pair `Zb n` (resp.
`Zc n`) picked out of the polygon `[Za n, Zb n, Zc n]` instead of `Za n`; this file records the
two missing arms.
-/
import Mathlib
import Submission.Work.ELNest.cut_mem_A
import Submission.Work.ELNest.cut_unique_A
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set

noncomputable section

namespace Work.ELAssembly

variable {c : ℂ}

/-- The boundary of the level-`n` region of the nest at `b₂` meets `K c` exactly in the three
cut points. -/
theorem frontier_D_inter_K (S : Work.ELNest.NestData c) (n : ℕ) :
    frontier (S.D n) ∩ Work.EL.K c =
      {z : ℂ | z = S.cutA n ∨ z = S.cutB n ∨ z = S.cutC n} := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hR : 1 < Work.ELNest.Dlev S.L n := by
    rw [Work.ELNest.Dlev]
    exact Real.one_lt_rpow S.hL (by positivity)
  have hC : Work.Top.IsJordanCurve
      (Work.EL.polyCurve [S.Za n, S.Zb n, S.Zc n] (Work.ELNest.Dlev S.L n)) :=
    Work.ELTop.polyCurve_isJordan S.d.hN _ (S.D_adm n) hR
  have hfr := Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ
    [S.Za n, S.Zb n, S.Zc n] (S.D_adm n) hR hC
  rw [show S.D n = Work.EL.polyRegion [S.Za n, S.Zb n, S.Zc n] (Work.ELNest.Dlev S.L n)
    from rfl, hfr]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, hP, hyz⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact Or.inl hyz.symm
    · exact Or.inr (Or.inl hyz.symm)
    · exact Or.inr (Or.inr hyz.symm)
  · rintro (rfl | rfl | rfl)
    · exact ⟨S.Za n, by simp, rfl⟩
    · exact ⟨S.Zb n, by simp, rfl⟩
    · exact ⟨S.Zc n, by simp, rfl⟩

/-- The pointwise form of `frontier_D_inter_K`: a point of `K c` on the boundary of the level-`n`
region is one of the three cut points. -/
theorem mem_frontier_D_iff (S : Work.ELNest.NestData c) (n : ℕ) (z : ℂ) :
    (z ∈ frontier (S.D n) ∧ z ∈ Work.EL.K c) ↔
      z = S.cutA n ∨ z = S.cutB n ∨ z = S.cutC n := by
  have h := frontier_D_inter_K S n
  rw [← Set.mem_inter_iff, h]
  simp

/-- **The cut point of the arm `B` lies in the arm `B`, in `K c` and on the boundary of the
level-`n` region.** -/
theorem cut_mem_B (S : Work.ELNest.NestData c) (n : ℕ) :
    S.cutB n ∈ S.armB ∩ Work.EL.K c ∩ frontier (S.D n) := by
  have hz := (mem_frontier_D_iff S n (S.cutB n)).mpr (Or.inr (Or.inl rfl))
  exact ⟨⟨S.cutB_mem n, hz.2⟩, hz.1⟩

/-- **The cut point of the arm `C` lies in the arm `C`, in `K c` and on the boundary of the
level-`n` region.** -/
theorem cut_mem_C (S : Work.ELNest.NestData c) (n : ℕ) :
    S.cutC n ∈ S.armC ∩ Work.EL.K c ∩ frontier (S.D n) := by
  have hz := (mem_frontier_D_iff S n (S.cutC n)).mpr (Or.inr (Or.inr rfl))
  exact ⟨⟨S.cutC_mem n, hz.2⟩, hz.1⟩

/-- **The cut point of the arm `B` is the only point of the arm `B` on the boundary of the
level-`n` region.** -/
theorem cut_unique_B (S : Work.ELNest.NestData c) (n : ℕ) :
    frontier (S.D n) ∩ Work.EL.K c ∩ S.armB = {S.cutB n} := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzfr, hzB⟩
    rcases (mem_frontier_D_iff S n z).mp hzfr with hz | hz | hz
    · exfalso
      have hzA : z ∈ S.armA := hz ▸ S.cutA_mem n
      exact (Set.disjoint_left.mp (Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).1 hzA) hzB
    · exact hz
    · exfalso
      have hzC : z ∈ S.armC := hz ▸ S.cutC_mem n
      exact (Set.disjoint_left.mp
        (Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).2.1 hzB) hzC
  · rintro rfl
    exact ⟨(mem_frontier_D_iff S n (S.cutB n)).mpr (Or.inr (Or.inl rfl)), S.cutB_mem n⟩

/-- **The cut point of the arm `C` is the only point of the arm `C` on the boundary of the
level-`n` region.** -/
theorem cut_unique_C (S : Work.ELNest.NestData c) (n : ℕ) :
    frontier (S.D n) ∩ Work.EL.K c ∩ S.armC = {S.cutC n} := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzfr, hzC⟩
    rcases (mem_frontier_D_iff S n z).mp hzfr with hz | hz | hz
    · exfalso
      have hzA : z ∈ S.armA := hz ▸ S.cutA_mem n
      exact (Set.disjoint_left.mp
        ((Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).2.2) hzC) hzA
    · exfalso
      have hzB : z ∈ S.armB := hz ▸ S.cutB_mem n
      exact (Set.disjoint_left.mp
        ((Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).2.1) hzB) hzC
    · exact hz
  · rintro rfl
    exact ⟨(mem_frontier_D_iff S n (S.cutC n)).mpr (Or.inr (Or.inr rfl)), S.cutC_mem n⟩

end Work.ELAssembly
