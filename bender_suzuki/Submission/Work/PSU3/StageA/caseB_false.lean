import Mathlib
import Submission.Work.PSU3.StageA.caseB_tQt_subset_of_Ksub
import Submission.Work.PSU3.StageA.not_caseB_false_of_Kset
import Submission.Work.PSU3.StageA.KOrbitsOfQ_full
import Submission.Work.PSU3.StageA.caseB_GoodReps_mem_Q0sub_iff
import Submission.Work.PSU3.StageA.caseB_GoodReps_ncard
import Submission.Work.PSU3.StageA.Ksub_cyclic_caseB
import Submission.Work.PSU3.StageA.caseB_orbits_conj_core
import Submission.Work.PSU3.StageA.caseB_canon_data_rrk
import Submission.Work.PSU3.StageA.HValueOfRRk
import Submission.Work.Higman.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option linter.unusedVariables false

/-- In the case-(b) configuration, `Kset H t` normalises `Q₀sub H`: conjugation by an element
of `Kset ⊆ twoPoint H t ≤ H` permutes the involutions of `H`, and `Q₀sub H = ⟨Inv H⟩` is
normal in `H` (`Work.ThmF.ChV12.Q0sub_elementary`). -/
theorem caseB_false_Q0norm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {a x : G} (ha : a ∈ Work.ThmF.Kset H t) (hx : x ∈ Work.ThmF.Q0sub H) :
    a⁻¹ * x * a ∈ Work.ThmF.Q0sub H := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hsplit
  obtain ⟨-, -, hnorm, -⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have haH : a ∈ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t ha)
  simpa only [inv_inv] using hnorm a⁻¹ (H.inv_mem haH) x hx

/-- The canonical form `t x t = a k t b` with `k ∈ Kset H t`, derived from the `K`-orbit
structure of `Q#` and the `d`-values on the representatives
(`caseB_tQt_subset_of_orbits_and_values`). -/
theorem caseB_false_canon {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (horbit : ∀ x ∈ Q, x ≠ 1 → ∃ k ∈ Work.ThmF.Kset H t,
      k⁻¹ * x * k ∈ Work.PSU3.StageA.GoodReps H t s r) :
    ∀ x ∈ Q, x ≠ 1 → ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * x * t = a * k * t * b := by
  have hr1 : r ≠ 1 := r_ne_one_of_hsr hS hs hr hsr
  have hvals : ∀ y ∈ Work.PSU3.StageA.GoodReps H t s r,
      ∃ a ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ b ∈ Q, t * y * t = a * k * t * b := by
    obtain ⟨h1, h2, h3, h4⟩ := caseB_dValue_reps hS hC4 hs hs2 hr hr1 hsr hKsub
    intro y hy
    rw [Work.PSU3.StageA.GoodReps] at hy
    rcases hy with hy | ⟨k, hkK, hk1, rfl⟩
    · rcases Set.mem_insert_iff.mp hy with hy | hy
      · rw [Set.mem_singleton_iff.mp hy]; exact h1
      · rcases Set.mem_insert_iff.mp hy with hy | hy
        · rw [Set.mem_singleton_iff.mp hy]; exact h2
        · rw [Set.mem_singleton_iff.mp hy]; exact h3
    · exact h4 k hkK hk1
  exact caseB_tQt_subset_of_orbits_and_values hS.split hKsub hs hs2 hr hsr horbit hvals

theorem caseB_false {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hW : Work.ThmF.W H t = ⊥)
    (hK : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) : False := by
  have hHig : Submission.Blueprint.HigmanProp := Work.Higman.higmanProp
  -- ### the counting input: `|GoodReps| = |Q₀| + 1`
  have hGood : (Work.PSU3.StageA.GoodReps H t s r).ncard
      = Nat.card (Work.ThmF.Q0sub H) + 1 :=
    caseB_GoodReps_ncard hS hC4 hs hs2 hr hsr h5 hK
  -- ### separatedness of the representatives
  have hsep : ∀ g₁ ∈ Work.PSU3.StageA.GoodReps H t s r,
      ∀ g₂ ∈ Work.PSU3.StageA.GoodReps H t s r, g₁ ≠ g₂ →
      ¬ ∃ k ∈ Work.ThmF.Kset H t, k⁻¹ * g₁ * k = g₂ := by
    intro g₁ hg₁ g₂ hg₂ hne ⟨k, hkK, hkconj⟩
    have hiff₁ := caseB_GoodReps_mem_Q0sub_iff hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hK hg₁
    have hiff₂ := caseB_GoodReps_mem_Q0sub_iff hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hK hg₂
    by_cases h1 : g₁ ∈ Work.ThmF.Q0sub H
    · have h2 : g₂ ∈ Work.ThmF.Q0sub H := hkconj ▸ caseB_false_Q0norm hS hC4 hkK h1
      exact hne ((hiff₁.mp h1).trans (hiff₂.mp h2).symm)
    · by_cases h2 : g₂ ∈ Work.ThmF.Q0sub H
      · have hkInv : k⁻¹ ∈ Work.ThmF.Kset H t := Kset_inv_mem hK hkK
        have h1' : g₁ ∈ Work.ThmF.Q0sub H := by
          have hmem : k * g₂ * k⁻¹ ∈ Work.ThmF.Q0sub H := by
            simpa only [inv_inv] using caseB_false_Q0norm hS hC4 hkInv h2
          rwa [show k * g₂ * k⁻¹ = g₁ from by rw [← hkconj]; group] at hmem
        exact hne ((hiff₁.mp h1').trans (hiff₂.mp h2).symm)
      · exact hne (caseB_orbits_conj_core hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hK
          hg₁ hg₂ h1 h2 hkK hkconj)
  -- ### the orbit structure of `Q#`
  have horbit : ∀ x ∈ Q, x ≠ 1 → ∃ k ∈ Work.ThmF.Kset H t,
      k⁻¹ * x * k ∈ Work.PSU3.StageA.GoodReps H t s r :=
    KOrbitsOfQ_of_sep hS hC4 hs hs2 hr hsr h5 hcard hK hsep hGood
  have hcanon := caseB_false_canon hS hC4 hs hs2 hr hsr hK horbit
  exact not_caseB_false_of_Kset hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hK hcanon

end Work.PSU3.StageA
