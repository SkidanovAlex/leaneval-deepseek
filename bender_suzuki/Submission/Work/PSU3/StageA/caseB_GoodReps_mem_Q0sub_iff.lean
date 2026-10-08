import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.PSU3.StageA.caseB_Ksub_action_coords
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.PSU3.StageA.Ksub_cyclic_caseB
import Submission.Work.PSU3.StageA.false_of_commuting_involutions

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseB_GoodReps_mem_Q0sub_iff`

In case b) of the Proposition of Peterfalvi II Ch. VI §1 (`Q` non-abelian of order
`|Q₀|² = |Q0sub H|²`, `orderOf (s*t) = 5`, `W = C_V(K) = ⊥`, `K = J(D,t)` a subgroup),
the representatives `GoodReps H t s r` of the `K`-orbits on `Q#` meet the elementary abelian
subgroup `Q₀ = Q0sub H` exactly in `s`:

`g ∈ GoodReps H t s r → (g ∈ Q0sub H ↔ g = s)`.

The two mathematical inputs are

* `r ∉ Q0sub H`: if `r ∈ Q0sub H` then `r` is an involution of `H` commuting with `t`
  (via the structure identity `t s t = r⁻¹ t r` and its consequence `t r t = r t s`,
  `caseB_t_conj_r`), contradicting strong embeddedness
  (`false_of_commuting_involutions`); while `s = r` would force `(s*t)³ = 1`, against
  `orderOf (s*t) = 5`.
* `r · r^{-k} ∉ Q0sub H` for `1 ≠ k ∈ Kset H t`: in the `𝔽_q`-coordinates `α : Q → F`
  of `caseB_Ksub_action_coords`, `α` is additive over `↥Q` and `α x = 0 ↔ x ∈ Q0sub H`,
  and `α (k⁻¹ x k) = κ k · α x`.  Hence
  `α (r · (k⁻¹ r⁻¹ k)) = α r + κ k · α (r⁻¹) = (1 - κ k) · α r`, which is nonzero because
  `α r ≠ 0` and `κ k ≠ 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs

theorem caseB_GoodReps_mem_Q0sub_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r g : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hg : g ∈ Work.PSU3.StageA.GoodReps H t s r) :
    (g ∈ Work.ThmF.Q0sub H ↔ g = s) := by
  classical
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs_sq
  have hs_mem : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hsplit.le hs, hs2⟩))

  -- ## `s ≠ r`
  have hsr_ne : s ≠ r := by
    intro hEq
    have hkey : t * s * t = s * t * s := by
      rw [← hEq] at hsr
      rw [hs_inv] at hsr
      exact hsr
    have h2 : (s * t) * (s * t) = t * s := by
      calc (s * t) * (s * t) = s * (t * s * t) := by group
        _ = s * (s * t * s) := by rw [hkey]
        _ = t * s := by
              rw [show s * (s * t * s) = (s * s) * (t * s) from by group, hs_sq]
              group
    have h3 : (s * t) ^ 3 = 1 := by
      have hj : (s * t) ^ 2 = t * s := by rw [pow_two]; exact h2
      rw [show (s * t) ^ 3 = (s * t) ^ 2 * (s * t) from by rw [pow_succ]]
      rw [hj]
      have h4 : (t * s) * (s * t) = t * t := by
        rw [show (t * s) * (s * t) = t * (s * s) * t from by group, hs_sq]
        group
      rw [h4, ht2]
    have hd : orderOf (s * t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
    rw [h5] at hd
    exact absurd hd (by norm_num)

  -- ## `r ∉ Q0sub H`
  have hr_not : r ∉ Work.ThmF.Q0sub H := by
    intro hr0
    have hr_sq : r * r = 1 := (Q0sub_structure hS hC4).1 r hr0
    have hr_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr_sq
    have hsr' : t * s * t = r * t * r := by
      have h := hsr
      rw [hr_inv] at h
      exact h
    have htrt : t * r * t = r * t * s := caseB_t_conj_r ht2 hs2 hsr
    have sr_comm : s * r = r * s := (Q0sub_structure hS hC4).2.1 s hs_mem r hr0
    have h1 : t * (s * r) * t = s * r := by
      have e1 : t * (s * r) * t = (t * s * t) * (t * r * t) := by
        rw [show (t * s * t) * (t * r * t) = t * s * (t * t) * r * t from by group, ht2]
        group
      rw [e1, hsr', htrt]
      rw [show (r * t * r) * (r * t * s) = r * t * (r * r) * t * s from by group, hr_sq]
      rw [show r * t * 1 * t * s = r * (t * t) * s from by group, ht2]
      rw [show r * 1 * s = r * s from by group]
      exact sr_comm.symm
    have hcomm : t * (s * r) = (s * r) * t := by
      have h2 : (t * (s * r) * t) * t = t * (s * r) := by
        rw [show (t * (s * r) * t) * t = t * (s * r) * (t * t) from by group, ht2, mul_one]
      rw [h1] at h2
      exact h2.symm
    have hu_sq : (s * r) ^ 2 = 1 := by
      rw [pow_two]
      rw [show s * r * (s * r) = s * (r * s) * r from by group, ← sr_comm]
      rw [show s * (s * r) * r = (s * s) * (r * r) from by group]
      rw [hs_sq, hr_sq, one_mul]
    have hu_ne : s * r ≠ 1 := by
      intro hu1
      apply hsr_ne
      have h := congrArg (fun z => z * r) hu1
      rw [show (s * r) * r = s * (r * r) from by group, hr_sq, mul_one, one_mul] at h
      exact h
    have hu2 : orderOf (s * r) = 2 := orderOf_eq_prime hu_sq hu_ne
    have huH : s * r ∈ H := hsplit.le (Q.mul_mem hs hr)
    exact false_of_commuting_involutions hS hsplit.invol hu2 hsplit.not_mem huH hcomm

  rw [GoodReps] at hg
  rcases hg with hg | ⟨k, hkK, hk1, rfl⟩
  · rcases (Set.mem_insert_iff.mp hg) with h1 | h1
    · subst h1
      exact ⟨fun _ => rfl, fun _ => hs_mem⟩
    · rcases (Set.mem_insert_iff.mp h1) with h2 | h2
      · subst h2
        exact ⟨fun h => absurd h hr_not, fun h => h ▸ hs_mem⟩
      · rw [Set.mem_singleton_iff] at h2
        subst h2
        exact ⟨fun h => absurd ((Work.ThmF.Q0sub H).inv_mem h) (by simpa using hr_not),
          fun h => h ▸ hs_mem⟩
  · constructor
    · intro hmem
      exfalso
      have hkKsub : k ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hkK
      have hkH : k ∈ H := Work.ThmF.ChV12.Ksub_le_H H t hkKsub
      have hcQ : k⁻¹ * r⁻¹ * k ∈ Q := by
        have hkN : k ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal hkH
        have hkinvN : k⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
          (Subgroup.normalizer (Q : Set G)).inv_mem hkN
        have h := (Subgroup.mem_normalizer_iff.mp hkinvN (r⁻¹)).mp (Q.inv_mem hr)
        simpa using h
      have hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t) :=
        Ksub_cyclic_caseB hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub
      obtain ⟨F, hF, hFint, α, κ, hcardF, hαsurj, hαadd, hαker, hαact⟩ :=
        caseB_Ksub_action_coords hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub hKcyc
      letI : Field F := hF
      have hαr : α ⟨r, hr⟩ ≠ 0 := fun h => hr_not ((hαker ⟨r, hr⟩).mp h)
      have hα1 : α (1 : ↥Q) = 0 := (hαker 1).mpr (Work.ThmF.Q0sub H).one_mem
      have hαrinv : α ⟨r⁻¹, Q.inv_mem hr⟩ = - α ⟨r, hr⟩ := by
        have h := hαadd ⟨r, hr⟩ ⟨r⁻¹, Q.inv_mem hr⟩
        have hmul : (⟨r, hr⟩ * ⟨r⁻¹, Q.inv_mem hr⟩ : ↥Q) = 1 := by
          apply Subtype.ext
          simp
        rw [hmul, hα1] at h
        exact eq_neg_of_add_eq_zero_right h.symm
      have hαk : α ⟨k⁻¹ * r⁻¹ * k, hcQ⟩
          = (κ ⟨k, hkKsub⟩ : F) * α ⟨r⁻¹, Q.inv_mem hr⟩ :=
        hαact ⟨k, hkKsub⟩ ⟨r⁻¹, Q.inv_mem hr⟩ ⟨k⁻¹ * r⁻¹ * k, hcQ⟩ rfl
      have hmem' : α (⟨r, hr⟩ * ⟨k⁻¹ * r⁻¹ * k, hcQ⟩) = 0 := by
        apply (hαker _).mpr
        simpa using hmem
      have heq : (1 - (κ ⟨k, hkKsub⟩ : F)) * α ⟨r, hr⟩ = 0 := by
        have h1 : (1 - (κ ⟨k, hkKsub⟩ : F)) * α ⟨r, hr⟩
            = α ⟨r, hr⟩ + (κ ⟨k, hkKsub⟩ : F) * (-(α ⟨r, hr⟩)) := by ring
        rw [h1, ← hαrinv, ← hαk, ← hαadd ⟨r, hr⟩ ⟨k⁻¹ * r⁻¹ * k, hcQ⟩]
        exact hmem'
      rcases mul_eq_zero.mp heq with h0 | h0
      · have hκk : κ ⟨k, hkKsub⟩ = 1 := (Units.ext (sub_eq_zero.mp h0)).symm
        have hk_eq : (⟨k, hkKsub⟩ : ↥(Work.ThmF.Ksub H t)) = 1 :=
          κ.injective (by simp [hκk])
        exact hk1 (Subtype.ext_iff.mp hk_eq)
      · exact hαr h0
    · intro h
      rw [h]
      exact hs_mem

end Work.PSU3.StageA
