import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.PSU3.StageA.caseB_canon_data_rrk
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.PSU3.StageA.caseB_GoodReps_Phi_inj
import Submission.Work.PSU3.StageA.caseB_GoodReps_s_notMem
import Submission.Work.PSU3.StageA.caseB_GoodReps_rinv_notMem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseB_GoodReps_ncard`

Peterfalvi II, Ch. VI §2 (p. 262): the set `GoodReps H t s r` of representatives of the
`K = Kset H t`-orbits on `Q#` — namely `s`, `r`, `r⁻¹`, and `r · r^{-k} = r · (k⁻¹ r⁻¹ k)`
for `1 ≠ k ∈ Kset H t` — has exactly `|K#| + 3 = q + 1` elements, `q = |Q₀| = |Q0sub H|`.

Since `|Kset H t| = |Q0sub H| - 1 = q - 1` (`Work.ThmF.Bender.cardKsetEqInv` plus
`card_Q0sub_eq`), the count follows from:

* `k ↦ r · (k⁻¹ r⁻¹ k)` is injective on `Kset H t`
  (`Work.PSU3.StageA.caseB_GoodReps_Phi_inj`);
* `s`, `r` and `r⁻¹` are pairwise distinct and lie outside the image
  (`caseB_GoodReps_s_notMem`, `caseB_GoodReps_rinv_notMem`, and `r · r ≠ 1`).

The last-mentioned input is the only place where `orderOf (s * t) = 5` is used: if `r * r = 1`
then, writing `u = t * r`, the structure identity gives `s * t = u * u` and the commutativity of
`s` and `r` (both lie in the elementary abelian `Q0sub H`) forces `u * u * u = (u * u * u)⁻¹`,
hence `orderOf u ∣ 6`; but `orderOf (u * u) = orderOf (s * t) = 5` divides `orderOf u`, and
`5 ∤ 6`.
-/

set_option autoImplicit false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- The map `k ↦ r · (k⁻¹ r⁻¹ k)` of Peterfalvi II Ch. VI §2 (the representative `r r^{-k}`). -/
def GoodRepsPhi {G : Type} [Group G] (r : G) : G → G := fun k => r * (k⁻¹ * r⁻¹ * k)

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}

/-- `r ≠ 1` for the structure-identity data `t * s * t = r⁻¹ * t * r` (if `r = 1` the identity
reads `s = t ∉ H`, against `s ∈ Q ≤ H`). -/
theorem caseB_GoodReps_r_ne_one (hS : Work.PSU3.PSU3Hyp H Q t) (hs : s ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r) : r ≠ 1 := by
  rintro rfl
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  have h1 : t * s * t = t := by simpa using hsr
  have h2 : s * t = 1 := by
    have h1' : t * (t * s * t) = 1 := by rw [h1, ht2]
    have key : t * (t * s * t) = s * t := by
      rw [show t * (t * s * t) = (t * t) * s * t from by group, ht2, one_mul]
    rwa [key] at h1'
  have hs_eq_t : s = t := by
    calc s = s * t * t := by rw [mul_assoc, ht2, mul_one]
      _ = 1 * t := by rw [h2]
      _ = t := one_mul t
  exact hS.split.not_mem (hs_eq_t ▸ hS.split.le hs)

/-- **`r * r ≠ 1`.**  For the structure-identity data of Ch. V §2 Lemma 1 with
`orderOf (s * t) = 5`, the element `r` is not an involution. -/
theorem caseB_GoodReps_r_sq_ne_one (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) : r * r ≠ 1 := by
  intro hr2
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  -- `s` and `r` commute: both lie in `Q0sub H`, which is abelian.
  have hsQ0 : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le hs, hs2⟩))
  have hcomm : s * r = r * s :=
    ((Work.ThmF.mem_centerOf (Q := Q)).mp (Q0sub_le_centerOf hS hC4 hsQ0)).2 r hr
  -- ## The pure group-theoretic computation, with `u = t * r`.
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set u : G := t * r with hu
  have htu : t * u = r := by rw [hu, ← mul_assoc, ht2, one_mul]
  have hF1 : s * t = u * u := by
    have h : t * s * t = r * t * r := by rw [hsr, hrinv]
    have e1 : s * t = t * (t * s * t) := by
      rw [show t * (t * s * t) = (t * t) * s * t from by group, ht2, one_mul]
    rw [e1, h, hu]
    group
  have hF4 : s = u * u * t := by
    have hst : s = (s * t) * t := by
      rw [show (s * t) * t = s * (t * t) from by group, ht2, mul_one]
    rw [hst, hF1]
  have hF3 : t * u * t = u⁻¹ := by
    have h : (t * u * t) * u = 1 := by
      rw [show (t * u * t) * u = (t * u) * (t * u) from by group, htu]
      exact hr2
    exact (inv_eq_of_mul_eq_one_left h).symm
  have hconj : (MulAut.conj t) u = u⁻¹ := by
    rw [MulAut.conj_apply, ht_inv]
    exact hF3
  have hG1 : s * r = u * u * u := by
    rw [hF4, ← htu]
    rw [show (u * u * t) * (t * u) = (u * u) * (t * t) * u from by group]
    simp only [ht2, mul_one]
  have hG2 : r * s = (u * u * u)⁻¹ := by
    rw [← htu, hF4]
    rw [show (t * u) * (u * u * t) = t * (u * u * u) * t from by group]
    rw [show t * (u * u * u) * t = (MulAut.conj t) (u * u * u) from by
      rw [MulAut.conj_apply, ht_inv]]
    rw [map_mul, map_mul, hconj]
    group
  have hw : u * u * u = (u * u * u)⁻¹ := hG1.symm.trans (hcomm.trans hG2)
  have hww : (u * u * u) * (u * u * u) = 1 :=
    (congrArg (fun z => (u * u * u) * z) hw).trans (mul_inv_cancel _)
  -- ## `orderOf u ∣ 6` and `orderOf (u * u) = 5`.
  have h6 : orderOf u ∣ 6 := by
    have hw2' : orderOf (u * u * u) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hww)
    have h3 : orderOf u ∣ 3 * orderOf (u * u * u) := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul, pow_three]
      rw [show u * (u * u) = u * u * u from by group]
      rw [pow_orderOf_eq_one]
    calc orderOf u ∣ 3 * orderOf (u * u * u) := h3
      _ ∣ 3 * 2 := mul_dvd_mul_left 3 hw2'
      _ = 6 := by norm_num
  have ho2 : orderOf (u * u) = 5 := by rw [← hF1]; exact h5
  have hdvd : orderOf (u * u) ∣ orderOf u := by
    rw [← pow_two]; exact orderOf_pow_dvd (x := u) 2
  have h56 : (5 : ℕ) ∣ 6 := by
    have := dvd_trans hdvd h6
    rwa [ho2] at this
  exact absurd h56 (by norm_num)

/-- **The cardinality of `GoodReps H t s r`** (Peterfalvi II Ch. VI §2, the source's count
`q + 1 = |K#| + 3`). -/
theorem caseB_GoodReps_ncard {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    (Work.PSU3.StageA.GoodReps H t s r).ncard = Nat.card (Work.ThmF.Q0sub H) + 1 := by
  classical
  have hr1 : r ≠ 1 := caseB_GoodReps_r_ne_one hS hs hsr
  have hr2 : r * r ≠ 1 := caseB_GoodReps_r_sq_ne_one hS hC4 hs hs2 hr hsr h5
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  -- `orderOf r ≠ 2`, so that `s`, `r`, `r⁻¹` are pairwise distinct.
  have hordr : orderOf r ≠ 2 := by
    intro h2
    exact hr2 (by have h := pow_orderOf_eq_one r; rw [h2, pow_two] at h; exact h)
  have hsne_sr : s ≠ r := fun h => hordr (by rw [← h]; exact hs2)
  have hsne_rinv : s ≠ r⁻¹ := fun h => hordr (by rw [← orderOf_inv, ← h]; exact hs2)
  have hrne_rinv : r ≠ r⁻¹ := by
    intro h
    exact hr2 (by simpa using congrArg (fun z => r * z) h)
  -- `|Kset H t| = q - 1`.
  have hKset : (Work.ThmF.Kset H t).ncard = Nat.card (Work.ThmF.Q0sub H) - 1 := by
    have h1 := Work.ThmF.Bender.cardKsetEqInv hS.split.stronglyEmbedded hS.split.invol
      hS.split.not_mem
    have h2 := card_Q0sub_eq hS hC4
    rw [h1, h2]
    omega
  -- `q ≥ 2` (`1 ≠ s ∈ Q0sub H`).
  have h2le : 2 ≤ Nat.card (Work.ThmF.Q0sub H) := by
    have hsQ0 : s ∈ Work.ThmF.Q0sub H :=
      Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le hs, hs2⟩))
    have hsub : ({1, s} : Set G) ⊆ (Work.ThmF.Q0sub H : Set G) := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact (Work.ThmF.Q0sub H).one_mem
      · rw [Set.mem_singleton_iff.mp hx]; exact hsQ0
    calc 2 = ({1, s} : Set G).ncard := (Set.ncard_pair (Ne.symm hs1)).symm
      _ ≤ (Work.ThmF.Q0sub H : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (Work.ThmF.Q0sub H) := Nat.card_coe_set_eq _
  -- Injectivity of `GoodRepsPhi r` on `Kset H t \ {1}`.
  have hInj : Set.InjOn (GoodRepsPhi r) (Work.ThmF.Kset H t \ {1}) :=
    fun a ha b hb h => caseB_GoodReps_Phi_inj hS hC4 hs hr hsr hKsub a ha.1 b hb.1 h
  -- The image has `q - 2` elements.
  have hT : (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})).ncard
      = Nat.card (Work.ThmF.Q0sub H) - 2 := by
    have himg : (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})).ncard
        = (Work.ThmF.Kset H t \ {1}).ncard :=
      (Set.ncard_image_iff (Set.toFinite _)).mpr hInj
    rw [himg, Set.ncard_sdiff_singleton_of_mem (Work.ThmF.one_mem_Kset H t), hKset]
    omega
  -- `{s, r, r⁻¹}` has three elements.
  have hA : ({s, r, r⁻¹} : Set G).ncard = 3 := by
    have h1 : s ∉ (insert r ({r⁻¹} : Set G)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hsne_sr, hsne_rinv⟩
    have h2 : r ∉ ({r⁻¹} : Set G) := by
      simpa only [Set.mem_singleton_iff] using hrne_rinv
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  -- `{s, r, r⁻¹}` is disjoint from the image.
  have hdisj : Disjoint ({s, r, r⁻¹} : Set G)
      (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})) := by
    rw [Set.disjoint_left]
    rintro x hx hxim
    rcases hxim with ⟨k, hk, rfl⟩
    obtain ⟨hkS, hk1⟩ := hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxs | hxr | hxri
    · exact caseB_GoodReps_s_notMem hS hC4 hs hs2 hr hr2 ⟨k, hkS, hxs⟩
    · -- `GoodRepsPhi r k = r` forces `r = 1`
      refine hr1 ?_
      have h : k⁻¹ * r⁻¹ * k = 1 := by
        have h := congrArg (fun z => r⁻¹ * z) hxr
        simpa [GoodRepsPhi, mul_assoc] using h
      have h' : r⁻¹ = 1 := by
        have h := congrArg (fun z => k * z * k⁻¹) h
        simpa [mul_assoc] using h
      exact inv_eq_one.mp h'
    · exact caseB_GoodReps_rinv_notMem (s := s) hS hr hr1 hr2 ⟨k, hkS, hxri⟩
  -- The defining set of `GoodReps` is the image of `Kset \ {1}`.
  have himg : {x : G | ∃ k : G, k ∈ Work.ThmF.Kset H t ∧ k ≠ 1
        ∧ x = r * (k⁻¹ * r⁻¹ * k)}
      = (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})) := by
    ext x
    constructor
    · rintro ⟨k, hk, hk1, rfl⟩
      exact ⟨k, ⟨hk, hk1⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hkS, hk1⟩ := hk
      exact ⟨k, hkS, hk1, rfl⟩
  have hset : Work.PSU3.StageA.GoodReps H t s r
      = ({s, r, r⁻¹} : Set G) ∪ (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})) := by
    simp only [Work.PSU3.StageA.GoodReps, himg]
  rw [hset]
  have hfinA : ({s, r, r⁻¹} : Set G).Finite := Set.toFinite _
  have hfinB : (GoodRepsPhi r '' (Work.ThmF.Kset H t \ {1})).Finite := Set.toFinite _
  rw [Set.ncard_union_eq hdisj hfinA hfinB, hA, hT]
  omega

end Work.PSU3.StageA
